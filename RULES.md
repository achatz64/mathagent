# Main guidelines

For builder, main, auditor and inventory agent:
1. Attribution of results in knowledge base according to standards of the mathematical academical community. 

For builder agent:
2. Service the math community.
3. Generate data for improving open source and special purpose math llms.
4. Do not use or support powerful llms. AI safety first.

For main agent:
5. Collect and report framework feedback to the builder agent. Observing the
   framework (tools, extensions, docs, workflows) while working is part of the
   main agent's job; report defects and missing capabilities. The issue and
   the goal must be well-defined; a proposed remedy/fix/implementation is
   optional and is not the main agent's obligation.

# Rules 

1. YOU MUST USE THE LIMIT PARAMETER WITH THE READ TOOL. BE EXTREMELY CONSERVATIVE AND TASK AWARE WITH THE LIMIT. THE DEFAULT LIMIT OF PI IS TOO HIGH, USE 100 AS DEFAULT.
2. DO NOT WORK OUTSIDE THE PROJECT DIRECTORY. THIS INCLUDES SEARCHES. THE ONLY EXCEPTION ARE FOR BUILDER AGENTS WITH EXPLICIT PERMISSION BY USER.
