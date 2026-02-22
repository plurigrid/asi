# Types

## AccountReferenceInput
Used everywhere to reference an account:
```graphql
input AccountReferenceInput {
  id: String        # Internal UUID
  legacyId: Int     # Legacy numeric ID
  slug: String      # URL slug (most common)
}
```

## Account (interface)
All account types implement this. Key fields:
- `id`, `legacyId`, `slug`, `name`, `legalName`, `type`
- `description`, `longDescription`, `tags`, `currency`
- `imageUrl(height)`, `backgroundImageUrl(height)`
- `website`, `socialLinks { type url }`
- `stats { balance, yearlyBudget, totalAmountReceived, totalAmountSpent, contributorsCount, activeRecurringContributions }`
- `members(role, limit, offset)` → `MemberCollection`
- `memberOf(role, limit, offset)` → `MemberOfCollection`
- `transactions(type, limit, offset)` → `TransactionCollection`
- `orders(status, limit, offset)` → `OrderCollection`
- `expenses(status, limit, offset)`
- `updates(limit, offset)`
- `tiers` → `TierCollection`
- `location { name address country lat long }`
- `policies`, `features`, `categories`

## Account Subtypes
`Collective`, `Organization`, `Individual`, `Fund`, `Event`, `Project`, `Host`, `Vendor`, `Bot`

Each adds specific fields. E.g., `Host` adds:
- `hostFeePercent`, `totalHostedCollectives`
- `hostedAccounts`, `hostApplications`
- `supportedPaymentMethods`, `supportedPayoutMethods`

## Expense
- `id`, `legacyId`, `description`, `longDescription`
- `type`: `INVOICE | RECEIPT | GRANT | SETTLEMENT | CHARGE`
- `status`: `DRAFT | UNVERIFIED | PENDING | APPROVED | PROCESSING | PAID | REJECTED | ERROR | SPAM | CANCELED | INCOMPLETE`
- `amount { valueInCents currency }`
- `items { id description amount url }`
- `attachedFiles { id url name }`
- `payee` → Account (who gets paid)
- `account` → Account (which collective pays)
- `createdByAccount` → Account
- `payoutMethod { type name data }`
- `activities`, `comments`, `tags`
- `createdAt`, `approvedAt`, `paidAt`

## Transaction
- `id`, `legacyId`, `type`: `CREDIT | DEBIT`
- `kind`: `CONTRIBUTION | EXPENSE | ADDED_FUNDS | HOST_FEE | PAYMENT_PROCESSOR_FEE | PLATFORM_FEE | BALANCE_TRANSFER`
- `amount`, `netAmount`, `taxAmount`, `platformFee`, `hostFee`, `paymentProcessorFee` — all `{ valueInCents currency }`
- `fromAccount`, `toAccount` → Account
- `expense`, `order` → linked objects
- `description`, `createdAt`

## Order
- `id`, `legacyId`, `status`: `NEW | PENDING | ACTIVE | CANCELLED | REJECTED | PAID | ERROR | EXPIRED`
- `frequency`: `ONETIME | MONTHLY | YEARLY`
- `totalAmount`, `amount` → `{ valueInCents currency }`
- `fromAccount`, `toAccount` → Account
- `tier` → Tier
- `createdAt`, `updatedAt`

## Member
- `id`, `role`: `ADMIN | MEMBER | CONTRIBUTOR | BACKER | ATTENDEE | FOLLOWER | ACCOUNTANT | HOST`
- `account` → Account (the member)
- `since`, `totalDonations { valueInCents currency }`
- `publicMessage`

## Tier
- `id`, `legacyId`, `name`, `slug`, `description`
- `type`: `TIER | MEMBERSHIP | DONATION | TICKET | SERVICE | PRODUCT`
- `amount { valueInCents currency }`, `amountType`: `FIXED | FLEXIBLE`
- `interval`: `month | year | flexible`
- `goal { valueInCents currency }`
- `maxQuantity`, `availableQuantity`

## Update
- `id`, `slug`, `title`, `summary`, `html`
- `publishedAt`, `createdAt`
- `fromAccount` → Account
- `comments`, `reactions`

## Amount
All monetary values use:
```graphql
type Amount {
  value: Float          # In major currency unit (dollars)
  valueInCents: Int     # In minor unit (cents) — prefer this
  currency: Currency    # ISO 4217 code
}
```

All enum values are listed inline with their parent types above.
