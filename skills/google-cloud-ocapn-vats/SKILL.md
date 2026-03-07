---
name: google-cloud-ocapn-vats
description: Google Cloud Platform API management for plurigrid.com org, framed as OCapN/CapTP vat topology. Covers org policy fixes, API enabling, and the full capability map of googleapis.com vats.
---

# Google Cloud OCapN Vats — plurigrid.com

GCP APIs as **CapTP vats**: each API is an unforgeable capability reference you spawn into your netlayer.

## Org Context

| Field | Value |
|-------|-------|
| Org | `plurigrid.com` — ID `737292068572` |
| Project | `native` — ID `merovingians` (number `302712368086`) |
| Old Project | `oldest` — ID `midyear-glazing-487407-t2` (number `321807517301`) |
| Account | `yuliya@plurigrid.com` |
| gcloud via | `flox install google-cloud-sdk` (env `v`) |

## Org Policy Fixes (already applied)

Two policies were blocking service account API key creation:

```bash
# 1. Deleted — was blocking SA JSON key creation
gcloud org-policies delete iam.disableServiceAccountKeyCreation \
  --organization=737292068572

# 2. Project-level override — Google-managed constraint
# Written to /tmp/policy-override.yaml then applied:
gcloud org-policies set-policy /tmp/policy-override.yaml
# policy: projects/midyear-glazing-487407-t2/policies/iam.managed.disableServiceAccountApiKeyCreation
# spec.rules: [{enforce: false}]

# Also granted orgpolicy.policyAdmin role (was missing despite being org admin):
gcloud organizations add-iam-policy-binding 737292068572 \
  --member="user:yuliya@plurigrid.com" \
  --role="roles/orgpolicy.policyAdmin"
```

> Note: `iam.managed.*` constraints don't appear in `gcloud org-policies list` — they're Google-managed. Override at project level with `enforce: false`.

## Enabling APIs

```bash
# Enable one
gcloud services enable secretmanager.googleapis.com \
  --project=midyear-glazing-487407-t2

# Enable many at once
gcloud services enable \
  secretmanager.googleapis.com \
  iamcredentials.googleapis.com \
  run.googleapis.com \
  pubsub.googleapis.com \
  generativelanguage.googleapis.com \
  cloudfunctions.googleapis.com \
  cloudkms.googleapis.com \
  cloudbuild.googleapis.com \
  --project=midyear-glazing-487407-t2

# List enabled
gcloud services list --enabled --project=midyear-glazing-487407-t2

# Count all available
gcloud services list --available --project=midyear-glazing-487407-t2 --format="value(name)" | wc -l
# => ~10,621 (513 googleapis.com, rest are marketplace)
```

## Currently Enabled Vats (34)

`aiplatform`, `analyticshub`, `artifactregistry`, `bigquery*` (7), `cloudapiregistry`, `cloudapis`, `cloudresourcemanager`, `cloudtrace`, `compute`, `dataflow`, `dataform`, `datalineage`, `dataplex`, `datastore`, `deploymentmanager`, `logging`, `monitoring`, `notebooks`, `orgpolicy`, `oslogin`, `servicemanagement`, `serviceusage`, `sql-component`, `storage*` (3), `telemetry`, `visionai`

## Available Vat Clusters (not yet enabled)

### AI & ML (+1 Generator vats)
`generativelanguage`, `documentai`, `speech`, `texttospeech`, `vision`, `videointelligence`, `language`, `translate`, `automl`, `ml`, `discoveryengine`, `recommendationengine`, `retail`, `contactcenteraiplatform`, `notebooksecurityscanner`

### Compute (Executor vats)
`run`, `cloudfunctions`, `appengine`, `batch`, `tpu`, `workstations`, `container`, `gkehub`, `vmwareengine`, `baremetalsolution`, `osconfig`

### Storage & Data (Cell vats — stateful)
`redis`, `memcache`, `spanner`, `alloydb`, `bigtable`, `firestore`, `sqladmin`, `storagetransfer`, `storageinsights`

### Security & Identity (-1 Validator vats)
`secretmanager`, `cloudkms`, `iamcredentials`, `recaptchaenterprise`, `certificatemanager`, `binaryauthorization`, `accessapproval`, `accesscontextmanager`, `webrisk`, `websecurityscanner`

### Messaging & Integration (0 Transport vats)
`pubsub`, `pubsublite`, `eventarc`, `workflows`, `cloudscheduler`, `cloudtasks`, `apigateway`, `apigee`, `connectors`, `integrations`

### Workspace (Live ref vats)
`gmail`, `drive`, `docs`, `sheets`, `slides`, `forms`, `calendar-json`, `chat`, `meet`, `vault`, `admin`, `alertcenter`

### Maps & Media (Observation vats)
`places`, `maps-backend`, `weather`, `airquality`, `geolocation`, `youtube`, `youtubeanalytics`, `streetviewpublish`

### DevOps (Lifecycle vats)
`cloudbuild`, `clouddeploy`, `sourcerepo`, `ondemandscanning`, `containeranalysis`

### Monitoring (Probe vats)
`clouderrorreporting`, `cloudprofiler`, `recommender`, `iap`

## CapTP Framing

```
GCP Org  = netlayer
Project  = vat container
API      = actor constructor (^behavior)
Enable   = spawn-vat
API Key  = sturdyref (survives restart)
IAM role = capability (unforgeable reference)
Org policy = membrane (attenuates capabilities)
```

GF(3) capability triads:
```
secretmanager (-1) ⊗ pubsub (0) ⊗ generativelanguage (+1) = 0 ✓  [Secure AI Pipeline]
cloudkms (-1) ⊗ run (0) ⊗ cloudfunctions (+1) = 0 ✓              [Serverless Compute]
iamcredentials (-1) ⊗ workflows (0) ⊗ eventarc (+1) = 0 ✓        [Event-driven]
```

## Useful Diagnostics

```bash
# Check org policies (custom only — managed ones won't appear)
gcloud org-policies list --organization=737292068572

# Describe specific policy
gcloud org-policies describe CONSTRAINT --organization=737292068572
gcloud org-policies describe CONSTRAINT --project=midyear-glazing-487407-t2

# Check account roles at org level
gcloud organizations get-iam-policy 737292068572 \
  --filter="bindings.members:yuliya@plurigrid.com" \
  --format="table(bindings.role)"
# Current roles: billing.creator, resourcemanager.organizationAdmin,
#                resourcemanager.projectCreator, orgpolicy.policyAdmin

# Create Vertex AI API key (now unblocked)
gcloud services api-keys create --display-name="Vertex AI Key" \
  --api-target=service=aiplatform.googleapis.com \
  --project=midyear-glazing-487407-t2
```
