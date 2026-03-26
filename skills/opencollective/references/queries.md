# Queries

## Account Details
```graphql
query GetAccount($slug: String!) {
  account(slug: $slug) {
    id name slug type description longDescription currency website
    imageUrl(height: 200)
    socialLinks { type url }
    tags categories
    stats {
      balance { valueInCents currency }
      yearlyBudget { valueInCents currency }
      yearlyBudgetManaged { valueInCents currency }
      totalAmountReceived { valueInCents currency }
      totalAmountSpent { valueInCents currency }
      activeRecurringContributions
      contributorsCount
    }
    members(role: [ADMIN], limit: 10) {
      nodes { account { name slug } role since }
    }
    tiers {
      nodes { id name slug description amount { valueInCents currency } interval goal { valueInCents currency } }
    }
  }
}
```

## Search Collectives
```graphql
query SearchCollectives($term: String!, $limit: Int) {
  accounts(searchTerm: $term, type: COLLECTIVE, limit: $limit, isActive: true) {
    totalCount
    nodes {
      name slug description currency
      stats { balance { valueInCents currency } contributorsCount }
      tags
    }
  }
}
```

## List Fiscal Hosts
```graphql
query ListHosts($limit: Int) {
  hosts(limit: $limit) {
    totalCount
    nodes {
      name slug description currency
      totalHostedCollectives
      stats { balance { valueInCents currency } }
      hostFeePercent
    }
  }
}
```

## Single Fiscal Host
```graphql
query GetHost($slug: String!) {
  host(slug: $slug) {
    name slug description currency hostFeePercent totalHostedCollectives
    stats { balance { valueInCents currency } }
    supportedPaymentMethods
    hostedAccounts(limit: 10) {
      totalCount
      nodes { name slug type stats { balance { valueInCents currency } } }
    }
  }
}
```

## Account Members (Backers/Sponsors)
```graphql
query GetMembers($slug: String!, $role: [MemberRole], $limit: Int!) {
  account(slug: $slug) {
    members(role: $role, limit: $limit) {
      totalCount
      nodes {
        account { name slug type imageUrl }
        role since totalDonations { valueInCents currency }
      }
    }
  }
}
```
Use `role: [BACKER]` for financial contributors, `[ADMIN]` for admins, `[MEMBER]` for core members.

## Expenses
```graphql
query GetExpenses($slug: String!, $status: ExpenseStatusFilter, $limit: Int!) {
  expenses(account: {slug: $slug}, status: $status, limit: $limit, orderBy: {field: CREATED_AT, direction: DESC}) {
    totalCount
    nodes {
      id description status type
      amount { valueInCents currency }
      createdAt
      createdByAccount { name slug }
      payee { name slug }
      items { description amount url }
      tags
    }
  }
}
```

## Single Expense Detail
```graphql
query GetExpense($id: String!) {
  expense(expense: {id: $id}) {
    id description longDescription status type
    amount { valueInCents currency }
    createdAt approvedAt paidAt
    createdByAccount { name slug }
    account { name slug }
    payee { name slug }
    payoutMethod { type name }
    items { id description amount url }
    activities { type createdAt individual { name } }
    comments(limit: 20) { nodes { html createdAt fromAccount { name } } }
    tags
  }
}
```

## Transactions
```graphql
query GetTransactions($slug: String!, $type: TransactionType, $limit: Int!) {
  transactions(account: {slug: $slug}, type: $type, limit: $limit, orderBy: {field: CREATED_AT, direction: DESC}) {
    totalCount
    nodes {
      id type kind description
      amount { valueInCents currency }
      netAmount { valueInCents currency }
      createdAt
      fromAccount { name slug type }
      toAccount { name slug type }
      expense { id description }
      order { id }
    }
  }
}
```

## Orders / Contributions
```graphql
query GetOrders($slug: String!, $status: [OrderStatus], $limit: Int!) {
  orders(account: {slug: $slug}, status: $status, limit: $limit) {
    totalCount
    nodes {
      id status frequency totalAmount { valueInCents currency }
      createdAt
      fromAccount { name slug }
      toAccount { name slug }
      tier { name slug }
    }
  }
}
```

## Updates / Blog Posts
```graphql
query GetUpdates($slug: String!, $limit: Int!) {
  updates(account: {slug: $slug}, limit: $limit, onlyPublishedUpdates: true) {
    totalCount
    nodes {
      id title slug summary publishedAt
      fromAccount { name slug }
      comments { totalCount }
      reactions
    }
  }
}
```

## Tag Stats / Ecosystem Exploration
```graphql
query TagStats($term: String, $limit: Int) {
  tagStats(searchTerm: $term, limit: $limit) {
    nodes { tag count }
  }
}
```

## Currency Exchange Rate
```graphql
query ExchangeRate($pair: CurrencyExchangeRateInput!) {
  currencyExchangeRate(requests: [$pair]) {
    value source date
  }
}
# Variable: { "pair": { "fromCurrency": "EUR", "toCurrency": "USD" } }
```

## Who Am I (requires auth)
```graphql
query {
  me {
    id name slug email
    memberOf(limit: 20) {
      nodes { role account { name slug type } }
    }
  }
}
```
