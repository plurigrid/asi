// Network Reconnaissance Tool
// Based on Black Hat Go Ch.2 (TCP), Ch.27 (IoT), Ch.33 (Reconnaissance)
// For geofence proofs and device fingerprinting

package main

import (
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"net"
	"os"
	"sort"
	"strings"
	"sync"
	"time"
)

// Device represents a discovered network device
type Device struct {
	IP        string            `json:"ip"`
	MAC       string            `json:"mac,omitempty"`
	Hostname  string            `json:"hostname,omitempty"`
	Vendor    string            `json:"vendor,omitempty"`
	OpenPorts []int             `json:"open_ports,omitempty"`
	Banners   map[int]string    `json:"banners,omitempty"`
	Services  map[int]string    `json:"services,omitempty"`
	TTL       int               `json:"ttl,omitempty"`
	Geofence  string            `json:"geofence,omitempty"`
	Timestamp time.Time         `json:"timestamp"`
}

// OUI database for device identification
var ouiDatabase = map[string]string{
	// Google/Waymo (subset)
	"F4:F5:D8": "Google",
	"00:1A:11": "Google",
	"00:F6:20": "Google",
	"08:9E:08": "Google",
	"30:FD:38": "Google",
	"D8:6C:63": "Google",
	// Tesla
	"4C:FC:AA": "Tesla",
	"54:9F:13": "Tesla",
	"98:ED:5C": "Tesla",
	// Espressif (IoT)
	"30:ED:A0": "Espressif",
	"24:6F:28": "Espressif",
	"AC:67:B2": "Espressif",
	// Bambu Lab (uses Espressif)
	// Ubiquiti
	"6C:63:F8": "Ubiquiti",
	"84:78:48": "Ubiquiti",
	// Apple
	"B0:BE:83": "Apple",
	"F0:18:98": "Apple",
}

// Geofence signatures
var geofenceSignatures = map[string][]string{
	"waymo":    {"Google", "Waymo"},
	"tesla":    {"Tesla"},
	"bambu":    {"Espressif"}, // Bambu uses Espressif chips
	"ubiquiti": {"Ubiquiti"},
}

// Common ports for IoT/embedded devices
var iotPorts = []int{
	22,   // SSH
	23,   // Telnet
	80,   // HTTP
	443,  // HTTPS
	990,  // FTPS (Bambu Lab)
	1883, // MQTT
	3000, // Node/Custom API (Bambu)
	5000, // UPnP/Custom
	5683, // CoAP
	6000, // Custom
	8080, // HTTP Alt
	8443, // HTTPS Alt
	8883, // MQTT TLS
	9000, // Custom
}

func lookupVendor(mac string) string {
	mac = strings.ToUpper(mac)
	prefix := mac[:8]
	if vendor, ok := ouiDatabase[prefix]; ok {
		return vendor
	}
	// Check if randomized (locally administered)
	firstByte, _ := hex.DecodeString(strings.Replace(mac[:2], ":", "", -1))
	if len(firstByte) > 0 && firstByte[0]&0x02 != 0 {
		return "Randomized"
	}
	return "Unknown"
}

func detectGeofence(vendor string) string {
	for geofence, vendors := range geofenceSignatures {
		for _, v := range vendors {
			if strings.Contains(vendor, v) {
				return geofence
			}
		}
	}
	return ""
}

func scanPort(ip string, port int, timeout time.Duration) bool {
	conn, err := net.DialTimeout("tcp", fmt.Sprintf("%s:%d", ip, port), timeout)
	if err != nil {
		return false
	}
	conn.Close()
	return true
}

func grabBanner(ip string, port int, timeout time.Duration) string {
	conn, err := net.DialTimeout("tcp", fmt.Sprintf("%s:%d", ip, port), timeout)
	if err != nil {
		return ""
	}
	defer conn.Close()
	
	conn.SetReadDeadline(time.Now().Add(timeout))
	
	// Send minimal probe
	switch port {
	case 80, 8080:
		conn.Write([]byte("GET / HTTP/1.0\r\n\r\n"))
	default:
		conn.Write([]byte("\n"))
	}
	
	buf := make([]byte, 512)
	n, _ := conn.Read(buf)
	if n > 0 {
		return strings.TrimSpace(string(buf[:n]))
	}
	return ""
}

func identifyService(port int, banner string) string {
	// Known signatures
	if strings.Contains(banner, "AirTunes") {
		return "AirPlay"
	}
	if strings.Contains(banner, `{"login"`) {
		return "Bambu-API"
	}
	if strings.Contains(banner, "HTTP") {
		return "HTTP"
	}
	if strings.Contains(banner, "SSH") {
		return "SSH"
	}
	if strings.Contains(banner, "220") && port == 21 {
		return "FTP"
	}
	
	// Default by port
	switch port {
	case 22:
		return "SSH"
	case 80, 8080:
		return "HTTP"
	case 443, 8443:
		return "HTTPS"
	case 990:
		return "FTPS"
	case 1883:
		return "MQTT"
	case 3000:
		return "API"
	case 5683:
		return "CoAP"
	}
	return "Unknown"
}

func scanDevice(ip string, timeout time.Duration) *Device {
	device := &Device{
		IP:        ip,
		Banners:   make(map[int]string),
		Services:  make(map[int]string),
		Timestamp: time.Now(),
	}
	
	// Parallel port scan
	var wg sync.WaitGroup
	var mu sync.Mutex
	
	for _, port := range iotPorts {
		wg.Add(1)
		go func(p int) {
			defer wg.Done()
			if scanPort(ip, p, timeout) {
				mu.Lock()
				device.OpenPorts = append(device.OpenPorts, p)
				mu.Unlock()
			}
		}(port)
	}
	wg.Wait()
	
	sort.Ints(device.OpenPorts)
	
	// Grab banners for open ports
	for _, port := range device.OpenPorts {
		banner := grabBanner(ip, port, timeout)
		if banner != "" {
			device.Banners[port] = banner[:min(200, len(banner))]
		}
		device.Services[port] = identifyService(port, banner)
	}
	
	return device
}

func scanNetwork(cidr string, timeout time.Duration) []*Device {
	ip, ipnet, err := net.ParseCIDR(cidr)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Invalid CIDR: %s\n", err)
		return nil
	}
	
	var devices []*Device
	var wg sync.WaitGroup
	var mu sync.Mutex
	semaphore := make(chan struct{}, 50) // Limit concurrency
	
	for ip := ip.Mask(ipnet.Mask); ipnet.Contains(ip); incIP(ip) {
		target := ip.String()
		wg.Add(1)
		semaphore <- struct{}{}
		
		go func(t string) {
			defer wg.Done()
			defer func() { <-semaphore }()
			
			// Quick ping check via TCP
			if scanPort(t, 80, timeout/2) || scanPort(t, 443, timeout/2) || scanPort(t, 22, timeout/2) {
				device := scanDevice(t, timeout)
				if len(device.OpenPorts) > 0 {
					mu.Lock()
					devices = append(devices, device)
					mu.Unlock()
				}
			}
		}(target)
	}
	wg.Wait()
	
	return devices
}

func incIP(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func main() {
	var (
		target  = flag.String("target", "", "Single IP to scan")
		network = flag.String("network", "", "CIDR to scan (e.g., 192.168.0.0/24)")
		timeout = flag.Duration("timeout", 2*time.Second, "Connection timeout")
		output  = flag.String("output", "text", "Output format: text, json")
		mac     = flag.String("mac", "", "MAC address to lookup vendor")
	)
	flag.Parse()
	
	// MAC lookup mode
	if *mac != "" {
		vendor := lookupVendor(*mac)
		geofence := detectGeofence(vendor)
		fmt.Printf("MAC: %s\nVendor: %s\nGeofence: %s\n", *mac, vendor, geofence)
		return
	}
	
	var devices []*Device
	
	if *target != "" {
		device := scanDevice(*target, *timeout)
		devices = append(devices, device)
	} else if *network != "" {
		fmt.Fprintf(os.Stderr, "Scanning %s...\n", *network)
		devices = scanNetwork(*network, *timeout)
	} else {
		flag.Usage()
		return
	}
	
	// Enrich with vendor info where possible
	for _, d := range devices {
		if d.MAC != "" {
			d.Vendor = lookupVendor(d.MAC)
			d.Geofence = detectGeofence(d.Vendor)
		}
	}
	
	// Output
	switch *output {
	case "json":
		enc := json.NewEncoder(os.Stdout)
		enc.SetIndent("", "  ")
		enc.Encode(devices)
	default:
		for _, d := range devices {
			fmt.Printf("\n=== %s ===\n", d.IP)
			if d.Vendor != "" {
				fmt.Printf("Vendor: %s\n", d.Vendor)
			}
			if d.Geofence != "" {
				fmt.Printf("Geofence: %s\n", d.Geofence)
			}
			fmt.Printf("Open Ports: %v\n", d.OpenPorts)
			for port, svc := range d.Services {
				fmt.Printf("  %d/%s", port, svc)
				if banner, ok := d.Banners[port]; ok && banner != "" {
					// Truncate banner for display
					if len(banner) > 60 {
						banner = banner[:60] + "..."
					}
					banner = strings.ReplaceAll(banner, "\n", " ")
					fmt.Printf(": %s", banner)
				}
				fmt.Println()
			}
		}
	}
}
