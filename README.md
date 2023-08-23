### Learning by Doing
Formalize the examples from chapter 2 of the book [PostgreSQL 14 Internals](https://postgrespro.com/community/books/internals) with TLA+. The interaction between database isolation levels and transactions can be very subtle. For even more complex transactions than those in the book, the process of formalization can be indispensable, especially in the design phase.

The heavy lifting has been done by two papers: [Seeing is Believing: A Client-Centric Specification of Database Isolation](https://dl.acm.org/doi/10.1145/3087801.3087802) and its formalization [Automated Validation of State-Based Client-Centric Isolation with TLA+](https://dl.acm.org/doi/abs/10.1007/978-3-030-67220-1_4). The code in this repo mainly just adapts them to the book.
