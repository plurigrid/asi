// Bambu Lab Protocol Dissector
// Based on Black Hat Go Ch.27 (IoT) and reverse engineering
// Protocol: Binary header (a5a5) + JSON payload

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net"
	"time"
)

// Bambu protocol magic bytes
var BambuMagic = []byte{0xa5, 0xa5}

// BambuHeader represents the protocol header
type BambuHeader struct {
	Magic   [2]byte
	Type    byte
	Padding byte
}

// BambuMessage represents a complete message
type BambuMessage struct {
	Header  BambuHeader
	Payload json.RawMessage
}

// LoginRequest for authentication
type LoginRequest struct {
	Login struct {
		SequenceID  int    `json:"sequence_id"`
		Command     string `json:"command"`
		Username    string `json:"username,omitempty"`
		Password    string `json:"password,omitempty"`
		AccessToken string `json:"access_token,omitempty"`
	} `json:"login"`
}

// PushingRequest for status/control
type PushingRequest struct {
	Pushing struct {
		SequenceID int    `json:"sequence_id"`
		Command    string `json:"command"`
	} `json:"pushing"`
}

// LoginResponse from printer
type LoginResponse struct {
	Login struct {
		SequenceID int    `json:"sequence_id"`
		Command    string `json:"command"`
		Status     string `json:"status"`
		Reason     string `json:"reason,omitempty"`
	} `json:"login"`
}

func parseHeader(data []byte) (*BambuHeader, error) {
	if len(data) < 4 {
		return nil, fmt.Errorf("data too short for header")
	}
	if !bytes.Equal(data[:2], BambuMagic) {
		return nil, fmt.Errorf("invalid magic: %x", data[:2])
	}
	return &BambuHeader{
		Magic:   [2]byte{data[0], data[1]},
		Type:    data[2],
		Padding: data[3],
	}, nil
}

func parseMessage(data []byte) (*BambuMessage, error) {
	header, err := parseHeader(data)
	if err != nil {
		return nil, err
	}
	
	// Find JSON start
	jsonStart := bytes.Index(data, []byte("{"))
	if jsonStart == -1 {
		return nil, fmt.Errorf("no JSON payload found")
	}
	
	// Find JSON end (last closing brace before trailer)
	jsonEnd := bytes.LastIndex(data, []byte("}"))
	if jsonEnd == -1 || jsonEnd <= jsonStart {
		return nil, fmt.Errorf("malformed JSON payload")
	}
	
	return &BambuMessage{
		Header:  *header,
		Payload: data[jsonStart : jsonEnd+1],
	}, nil
}

func buildMessage(msgType byte, payload interface{}) ([]byte, error) {
	jsonData, err := json.Marshal(payload)
	if err != nil {
		return nil, err
	}
	
	var buf bytes.Buffer
	buf.Write(BambuMagic)
	buf.WriteByte(msgType)
	buf.WriteByte(0x00)
	buf.Write(jsonData)
	
	return buf.Bytes(), nil
}

func sendReceive(conn net.Conn, msg []byte, timeout time.Duration) ([]byte, error) {
	conn.SetDeadline(time.Now().Add(timeout))
	
	_, err := conn.Write(msg)
	if err != nil {
		return nil, err
	}
	
	buf := make([]byte, 4096)
	n, err := conn.Read(buf)
	if err != nil {
		return nil, err
	}
	
	return buf[:n], nil
}

// ProbeDevice attempts to gather info from a Bambu printer
func ProbeDevice(ip string, port int) (*DeviceInfo, error) {
	conn, err := net.DialTimeout("tcp", fmt.Sprintf("%s:%d", ip, port), 5*time.Second)
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	
	info := &DeviceInfo{IP: ip, Port: port}
	
	// Try pushall command (works without auth on some firmware)
	pushReq := PushingRequest{}
	pushReq.Pushing.SequenceID = 1
	pushReq.Pushing.Command = "pushall"
	
	msg, _ := buildMessage(0xa1, pushReq)
	resp, err := sendReceive(conn, msg, 3*time.Second)
	if err == nil {
		info.RawResponse = resp
		if parsed, err := parseMessage(resp); err == nil {
			info.ParsedResponse = parsed
		}
	}
	
	return info, nil
}

type DeviceInfo struct {
	IP             string
	Port           int
	RawResponse    []byte
	ParsedResponse *BambuMessage
}

// Protocol constants discovered through reverse engineering
const (
	MsgTypeLogin   = 0xa1
	MsgTypePush    = 0xa2
	MsgTypeControl = 0xa3
)

func main() {
	fmt.Println("Bambu Protocol Dissector")
	fmt.Println("========================")
	
	// Example: parse captured data
	captured := []byte{
		0xa5, 0xa5, 0xa1, 0x00,
		'{', '"', 'l', 'o', 'g', 'i', 'n', '"', ':', '{', '}', '}',
	}
	
	msg, err := parseMessage(captured)
	if err != nil {
		fmt.Printf("Parse error: %v\n", err)
		return
	}
	
	fmt.Printf("Header: magic=%x type=%02x\n", msg.Header.Magic, msg.Header.Type)
	fmt.Printf("Payload: %s\n", msg.Payload)
	
	// Protocol documentation
	fmt.Println("\nProtocol Structure:")
	fmt.Println("  [2 bytes] Magic: 0xa5a5")
	fmt.Println("  [1 byte]  Type:  0xa1=login, 0xa2=push, 0xa3=control")
	fmt.Println("  [1 byte]  Pad:   0x00")
	fmt.Println("  [n bytes] JSON payload")
	fmt.Println("  [2 bytes] Trailer: 0xa7a7 (optional)")
	
	fmt.Println("\nKnown Commands:")
	fmt.Println("  login: {\"login\":{\"sequence_id\":N,\"command\":\"CMD\"}}")
	fmt.Println("  push:  {\"pushing\":{\"sequence_id\":N,\"command\":\"pushall\"}}")
	
	// TLS on port 990
	fmt.Println("\nPort 990 (FTPS):")
	fmt.Println("  Certificate CN: 01P00C543001592 (printer serial)")
	fmt.Println("  Issuer: BBL Technologies Co., Ltd")
	fmt.Println("  This is the secure file transfer port for print files")
	
	// Port 8883 = MQTT over TLS
	fmt.Println("\nPort 8883 (MQTT-TLS):")
	fmt.Println("  Standard MQTT over TLS port")
	fmt.Println("  Used for cloud connectivity to Bambu Cloud")
}
