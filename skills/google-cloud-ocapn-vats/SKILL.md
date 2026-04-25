---
name: google-cloud-ocapn-vats
description: "Google Cloud Platform project and API management for plurigrid.com org. Use when enabling GCP APIs, managing org policies, creating service accounts or API keys, or working with Google Cloud projects."
---

# Google Cloud — plurigrid.com

## Org & Project Structure

| Field | Value |
|-------|-------|
| Org | `plurigrid.com` -- ID `737292068572` |
| Project | `native` -- ID `merovingians` (number `302712368086`) |
| Old Project | `oldest` -- ID `midyear-glazing-487407-t2` (number `321807517301`) |
| Account | `yuliya@plurigrid.com` |
| gcloud via | `flox install google-cloud-sdk` (env `v`) |

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

# Count all available (~10,621: 513 googleapis.com + marketplace)
gcloud services list --available --project=midyear-glazing-487407-t2 --format="value(name)" | wc -l
```

## Currently Enabled (34)

`aiplatform`, `analyticshub`, `artifactregistry`, `bigquery*` (7), `cloudapiregistry`, `cloudapis`, `cloudresourcemanager`, `cloudtrace`, `compute`, `dataflow`, `dataform`, `datalineage`, `dataplex`, `datastore`, `deploymentmanager`, `logging`, `monitoring`, `notebooks`, `orgpolicy`, `oslogin`, `servicemanagement`, `serviceusage`, `sql-component`, `storage*` (3), `telemetry`, `visionai`

## Org Policy Notes

- `iam.managed.*` constraints do NOT appear in `gcloud org-policies list` -- they are Google-managed. Override at project level with `enforce: false` via `gcloud org-policies set-policy`.
- SA key creation was previously blocked by `iam.disableServiceAccountKeyCreation` (deleted) and `iam.managed.disableServiceAccountApiKeyCreation` (overridden at project level).

## Diagnostics

```bash
# Check org policies (custom only -- managed ones won't appear)
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

# Create API key (SA key creation now unblocked)
gcloud services api-keys create --display-name="Vertex AI Key" \
  --api-target=service=aiplatform.googleapis.com \
  --project=midyear-glazing-487407-t2
```


## ACP atlas

Part of: `acp-commons`.
