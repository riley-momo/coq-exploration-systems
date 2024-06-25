# A Tale of Two Proofs: A Systems-Modelling Exploration of Coq

This work was done as part of my PhD research when exploring interactive theorem provers (ITPs). I am publishing it publcily here in case others may benefit from it, as ITPs can be an overwhelming field to get into. In order to become more familiar with practical usage of Coq, I decided to examine the proofs provided in the paper *Formal proofs applied to system models* Contejean, É., & Samokish, A. (2023). I found the motivation and vision for this paper to be very compelling, but was struck that they did not include their actual Coq code. In light of this, I wanted to make sure others could replicate the kind of proofs they demonstrate, and to do so in a simplified way for Coq newcomers as well.
In the work I present here, I explore Coq, motivated by this paper, by creating an example system specification of a steam generator system in a nuclear reactor. I then go on to prove properties of the . You can read my full explanation in the pdf provided here, and view the accompanying Coq code in the .v file. 

## Contents
1. Coq Systems Exploration.pdf - the PDF writeup to accompany this repository, written in a tutorial style so those with zero Coq experience can grasp the concepts being demonstrated and try Coq proofs out for themselves.

2. system_demo.v - the Coq file containg the code referenced in the writeup, it includes inductive types and instantiations to model an example system of a steam generator used in a nuclear generator system.

3. readme.md - the readme file you are currently viewing.


## References

Contejean, É., & Samokish, A. (2023). *Formal proofs applied to system models*. In *JFLA 2023-34èmes Journées Francophones des Langages Applicatifs* (pp. 121-133).
