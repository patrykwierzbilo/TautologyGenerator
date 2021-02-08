# Tautology generator

Program for generating all possible tautologies with at most two variables.

# Working

The program generates all possible logical expressions with the brute force method (low efficiency due to exponential complexity), it generates all possible evaluations through the truth table. If the expression is always true it is a tautology.

Logical expressions support the following operators:

| Operators             | Representation |
|:----------------------|:--------------:|
| Negation              | !              |
| And                   | &              |
| Or                    | \|             |
| Implication           | >              |
| Equality              | #              |

# Usage

```
$ tautGen N <filename>
```

-N is the maximum length of the expression (tautologies from 1 to N will be generated)

-The second argument is the name of the file where the result will be written

The tautology also includes parentheses. The length of a tautology is the number of symbols it contains, e.g. (p>q)|p has a length of 7.