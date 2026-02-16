---
name: k3s-backup
description: |
  Backup and recovery solution for K3s clusters. Includes scheduled, pre-shutdown, and manual backup strategies with recovery procedures.
license: MIT
tags:
  - k3s
  - kubernetes
  - backup
  - recovery
  - disaster-recovery
  - sqlite
  - cluster
metadata:
  author: Stakpak <team@stakpak.dev>
  version: "1.0.0"
---

# K3s Backup & Recovery

## Quick Start

### Manual Backup

```bash
sudo /usr/local/bin/k3s-backup.sh
ls -lh /backup/k3s/
```

### Quick Recovery

```bash
sudo /root/k3s-recovery.sh $(ls -t /backup/k3s/*.tar.gz | head -1)
```

## Cluster Overview

* **Master Node**: Control plane node running K3s server
* **Worker Nodes**: Worker nodes running K3s agent
* **Database**: SQLite (not etcd)
* **Backup Location**: `/backup/k3s/` on master node

## Backup Strategy

### Triple Protection System

| Type | Schedule | Trigger | Downtime |
|------|----------|---------|----------|
| Scheduled | Daily 2:00 AM | Cron job | ~30 sec |
| Pre-Shutdown | Before reboot/shutdown | Systemd service | ~30 sec |
| Manual | On-demand | Command | ~30 sec |

### What Gets Backed Up

**Included:**
* K3s server database (`/var/lib/rancher/k3s/server/db/`)
* Node token and certificates
* K3s configuration files (`/etc/rancher/k3s/`)
* All Kubernetes manifests and resources
* Network and storage configurations

**Not Included:**
* Container images (re-downloaded on restore)
* Persistent Volume data (needs separate backup)
* Application-specific data in pods

## Components

### 1. Backup Script

**Location**: `/usr/local/bin/k3s-backup.sh`

```bash
#!/bin/bash
BACKUP_DIR="/backup/k3s"
DATE=$(date +%Y%m%d-%H%M%S)

mkdir -p $BACKUP_DIR

systemctl stop k3s

tar -czf $BACKUP_DIR/k3s-backup-$DATE.tar.gz \
    /var/lib/rancher/k3s/server/ \
    /etc/rancher/k3s/

systemctl start k3s

ls -t $BACKUP_DIR/k3s-backup-*.tar.gz | tail -n +11 | xargs -r rm

echo "Backup completed: k3s-backup-$DATE.tar.gz"
```

### 2. Recovery Script

**Location**: `/root/k3s-recovery.sh`

```bash
#!/bin/bash
BACKUP_FILE=$1

if [ -z "$BACKUP_FILE" ]; then
    echo "Usage: $0 /backup/k3s/k3s-backup-TIMESTAMP.tar.gz"
    ls -lh /backup/k3s/
    exit 1
fi

echo "Stopping K3s..."
systemctl stop k3s

echo "Removing old data..."
rm -rf /var/lib/rancher/k3s/server/
rm -rf /etc/rancher/k3s/

echo "Restoring from $BACKUP_FILE..."
tar -xzf $BACKUP_FILE -C /

echo "Starting K3s..."
systemctl start k3s

sleep 30

echo "Verifying cluster..."
kubectl get nodes
kubectl get pods -A

echo "Recovery complete!"
```

### 3. Scheduled Backup (Cron)

**Location**: `/etc/crontab`

```cron
0 2 * * * root /usr/local/bin/k3s-backup.sh >> /var/log/k3s-backup.log 2>&1
```

### 4. Pre-Shutdown Service

**Location**: `/etc/systemd/system/k3s-pre-shutdown.service`

```ini
[Unit]
Description=K3s Pre-Shutdown Backup
DefaultDependencies=no
Before=shutdown.target reboot.target halt.target

[Service]
Type=oneshot
ExecStart=/usr/local/bin/k3s-backup.sh
TimeoutStartSec=300

[Install]
WantedBy=halt.target reboot.target shutdown.target
```

## Installation

### Setup Scripts

```bash
# 1. Create backup script
sudo tee /usr/local/bin/k3s-backup.sh << 'EOF'
[script content]
EOF
sudo chmod +x /usr/local/bin/k3s-backup.sh

# 2. Create recovery script
sudo tee /root/k3s-recovery.sh << 'EOF'
[script content]
EOF
sudo chmod +x /root/k3s-recovery.sh

# 3. Add cron job
echo "0 2 * * * root /usr/local/bin/k3s-backup.sh >> /var/log/k3s-backup.log 2>&1" | sudo tee -a /etc/crontab

# 4. Create and enable pre-shutdown service
sudo tee /etc/systemd/system/k3s-pre-shutdown.service << 'EOF'
[service content]
EOF
sudo systemctl enable k3s-pre-shutdown.service
```

### Verification

```bash
ls -l /usr/local/bin/k3s-backup.sh
ls -l /root/k3s-recovery.sh
cat /etc/crontab | grep k3s-backup
sudo systemctl status k3s-pre-shutdown.service
sudo systemctl is-enabled k3s-pre-shutdown.service
```

## Usage

### Manual Backup

```bash
sudo /usr/local/bin/k3s-backup.sh
ls -lh /backup/k3s/
tail -f /var/log/k3s-backup.log
```

### Scheduled Backup

* Automatic daily backup at 2:00 AM
* Check logs: `cat /var/log/k3s-backup.log`
* Verify: `ls -lt /backup/k3s/ | head -5`

### Pre-Shutdown Backup

* Automatically runs before graceful shutdown/reboot
* Verify after reboot: `ls -lt /backup/k3s/ | head -5`
* Check logs: `sudo journalctl -u k3s-pre-shutdown.service -b -1`

## Recovery Procedures

### Standard Recovery

```bash
# List backups
ls -lh /backup/k3s/

# Restore from specific backup
BACKUP_FILE="/backup/k3s/k3s-backup-TIMESTAMP.tar.gz"
sudo /root/k3s-recovery.sh $BACKUP_FILE

# Verify cluster
kubectl get nodes
kubectl get pods -A
kubectl get pv,pvc -A
```

### Quick Recovery (Latest Backup)

```bash
sudo /root/k3s-recovery.sh $(ls -t /backup/k3s/*.tar.gz | head -1)
```

### Partial Recovery

```bash
# List backup contents
sudo tar -tzf /backup/k3s/k3s-backup-TIMESTAMP.tar.gz | less

# Extract specific files
sudo tar -xzf /backup/k3s/k3s-backup-TIMESTAMP.tar.gz \
    var/lib/rancher/k3s/server/node-token \
    -C / --strip-components=0
```

### Recovery After Complete Failure

```bash
# 1. Reinstall K3s on master node
curl -sfL https://get.k3s.io | K3S_TOKEN=<your-token> sh -s - server --disable=traefik --tls-san <master-ip> --advertise-address <master-ip> --node-external-ip <master-ip>

# 2. Stop K3s
sudo systemctl stop k3s

# 3. Run recovery
sudo /root/k3s-recovery.sh /path/to/backup.tar.gz

# 4. Verify and rejoin workers if needed
kubectl get nodes
ssh <worker-user>@<worker-ip> "sudo systemctl restart k3s-agent"
```

### Recovery Timeline

| Step | Duration |
|------|----------|
| Stop K3s | ~5 seconds |
| Remove old data | ~10 seconds |
| Restore backup | ~20-40 seconds |
| Start K3s | ~30 seconds |
| Verify cluster | ~30 seconds |
| **Total** | **~2 minutes** |

## Emergency Recovery

### Quick Recovery Command

```bash
sudo /root/k3s-recovery.sh $(ls -t /backup/k3s/*.tar.gz | head -1)
```

## References

* [K3s Official Documentation](https://docs.k3s.io/)
* [K3s Backup/Restore Guide](https://docs.k3s.io/datastore/backup-restore)
* [Kubernetes Disaster Recovery](https://kubernetes.io/docs/tasks/administer-cluster/configure-upgrade-etcd/#backing-up-an-etcd-cluster)