# Processor

This repository presents a functional, but soon-to-be fully-realized model of a 32-bit processor developed entirely from first principles. 
A finite-state automaton (FSA) was used to model the processor. Then, [sequential logical expressions](https://github.com/Amjad-H-Ali/Processor/blob/main/model.txt) were derived from said automaton. Future enhancements will include a formal specification and verifiication of the processor in [TLA+/TLAPS](https://lamport.azurewebsites.net/tla/tla.html).
The end goal of this project is a practical, formally verified, Turing complete processor built on an FPGA.

In this repository, you will find:

* [A Simulink file](https://github.com/Amjad-H-Ali/Processor/blob/main/PROCESSOR.slx) : Simulink is a MATLAB-based software for modeling and simulating systems and will need to be [installed](https://www.mathworks.com/help/install/install-products.html). The interactive version of the FSA was designed in Simulink and looks like this:

<h6>Abstract overview of the FSA </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/PROC_MODEL_SIMULINK.png?raw=true)

<h6> Detailed FSA of the Multiplier </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/MULT_MODEL_SIMULINK.png?raw=true)

<h6> Detailed FSA of the Adder </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/ADDER_MODEL_SIMULINK.png?raw=true)

* [An OmniGraffle file](https://github.com/Amjad-H-Ali/Processor/blob/main/PROCESSOR_MODEL_FSA.graffle) : OmniGraffle is a tool for building visual diagrams and can be installed [here](https://www.omnigroup.com/omnigraffle). The non-interactive FSA was designed in OmniGraffle and looks like this:

<h6> FSA of the Multiplier </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/MULT_MODEL_GRAFFLE.png?raw=true)

<h6> FSA of the Adder </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/ADDER_MODEL_GRAFFLE.png?raw=true)

* [TLA file](https://github.com/Amjad-H-Ali/Processor/blob/main/model.tla) : TLA+ is a language designed to model systems using basic mathematics. TLAPS is a system for writing and checking formal proofs for said model. TLA+ and TLAPS can be installed [here](https://lamport.azurewebsites.net/tla/tla.html). It looks something like this:

<h6> Mathematical expression for variable xR11 </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/r11_expression_tla_sample.png?raw=true)

<h6> Sample proof that CMP32 is correct </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/tla_thm_sample.png?raw=true)

<h6> TLA+ can easily convert to LaTeX </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/model_latex_thm_sample.png?raw=true)

* [PDF file](https://github.com/Amjad-H-Ali/Processor/blob/main/model.pdf) : This file is the TLA+ specification in LaTeX form.

<h6> Specification of XOR and CMP in LaTeX </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/logic_latex_sample.png?raw=true)

* [processor.asm](https://github.com/Amjad-H-Ali/Processor/blob/main/processor.asm) : This file will eventually conain the full processor written in x86_64 assembly. Although the final goal is to have a physical processor on an FPGA, it would be nice to have a software version of the processor for simulation. The entire processor model was designed in a way so that it would only need to use registers for its internal build. It only needs registers R8-R15 on the x86_64 architecture for storing model input/output variables, and floating point registers XMM0-XMM15 for storing its own 32-bit registers. Registers RAX, RBX, RCX, RDX, RSI and RDI on the x86_64 processor can be used for computing logic or as temporary storage units. This is not to say the processor does not use other sources of memory at all (like RAM or cache). The processor will use RAM or cache when fetching an instruction or executing a load/store instruction. What is meant here is that the algorithms used to build the processor only use x86_64 register memory.

* [model.txt](https://github.com/Amjad-H-Ali/Processor/blob/main/model.txt) : This is a text file containing the logical expression that make up the model.

* [scripts.js](https://github.com/Amjad-H-Ali/Processor/blob/main/scripts.js) : This file contains some random JS scripts that help automate writing some logical expressions that otherwise would have been a laborious task doing it by hand.


## The Instruction Set Architecture (ISA)

Every instruction is 64-bits wide and is identified and checked for format in the Decode stage of the processor.

<table>
  <tr>
    <td>BITS</td>
    <td>0</td>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
    <td>6</td>
    <td>7</td>
    <td>8</td>
    <td>9</td>
    <td>10</td>
    <td>11</td>
    <td>12</td>
    <td>13</td>
    <td>14</td>
    <td>15</td>
    <td>16</td>
    <td>17</td>
    <td>18</td>
    <td>19</td>
    <td>20</td>
    <td>21</td>
    <td>22</td>
    <td>23</td>
    <td>24</td>
    <td>25</td>
    <td>26</td>
    <td>27</td>
    <td>28</td>
    <td>29</td>
    <td>30</td>
    <td>31</td>
    <td>32</td>
    <td>33</td>
    <td>34</td>
    <td>35</td>
    <td>36</td>
    <td>37</td>
    <td>38</td>
    <td>39</td>
    <td>40</td>
    <td>41</td>
    <td>42</td>
    <td>43</td>
    <td>44</td>
    <td>45</td>
    <td>46</td>
    <td>47</td>
    <td>48</td>
    <td>49</td>
    <td>50</td>
    <td>51</td>
    <td>52</td>
    <td>53</td>
    <td>54</td>
    <td>55</td>
    <td>56</td>
    <td>57</td>
    <td>58</td>
    <td>59</td>
    <td>60</td>
    <td>61</td>
    <td>62</td>
    <td>63</td>
  </tr>
     
  <tr>
    <td>INSTRUCTION </td>
    <td colspan="8">ICODE</td>
    <td colspan="56"></td>
  </tr>
  <tr>
    <td>mov rA,D(rB,rC,s)</td>
    <td colspan="8">0</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="5">rC</td>
    <td colspan="4">s</td>
    <td colspan="32">D</td>
    <td colspan="5">PADDING</td>
   </tr>
  
   <tr>
    <td>mov D(rB,rC,s),rA</td>
    <td colspan="8">1</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="5">rC</td>
    <td colspan="4">s</td>
    <td colspan="32">D</td>
     <td colspan="5">PADDING</td>
  </tr>
  
  <tr>
    <td>lea rA,D(rB,rC,s)</td>
    <td colspan="8">2</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="5">rC</td>
    <td colspan="4">s</td>
    <td colspan="32">D</td>
    <td colspan="5">PADDING</td>
  </tr>  
  <tr>
    <td>mov rA,D(rB)</td>
    <td colspan="8">9</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="32">D</td>
    <td colspan="14">PADDING</td>
  </tr> 
  <tr>
    <td>mov D(rB),rA</td>
    <td colspan="8">10</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="32">D</td>
    <td colspan="14">PADDING</td>
  </tr> 
  
  <tr>
    <td>mov rA,rB</td>
    <td colspan="8">17</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>movl rA,rB</td>
    <td colspan="8">18</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>movle rA,rB</td>
    <td colspan="8">19</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>movg rA,rB</td>
    <td colspan="8">20</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>movge rA,rB</td>
    <td colspan="8">21</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>move rA,rB</td>
    <td colspan="8">22</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>movne rA,rB</td>
    <td colspan="8">23</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>and rA,rB</td>
    <td colspan="8">24</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>or rA,rB</td>
    <td colspan="8">25</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>xor rA,rB</td>
    <td colspan="8">26</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>shl rA,rB</td>
    <td colspan="8">27</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>shr rA,rB</td>
    <td colspan="8">28</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>sar rA,rB</td>
    <td colspan="8">29</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>add rA,rB</td>
    <td colspan="8">30</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>sub rA,rB</td>
    <td colspan="8">31</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>mult rA,rB</td>
    <td colspan="8">32</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>cmp rA,rB</td>
    <td colspan="8">33</td>
    <td colspan="5">rA</td>
    <td colspan="5">rB</td>
    <td colspan="46">PADDING</td>
  </tr>
  <tr>
    <td>mov rA,imm</td>
    <td colspan="8">44</td>
    <td colspan="5">rA</td>
    <td colspan="32">IMMEDIATE</td>
    <td colspan="19">PADDING</td>
  </tr>
  <tr>
    <td>not rA</td>
    <td colspan="8">51</td>
    <td colspan="5">rA</td>
    <td colspan="51">PADDING</td>
  </tr>
  <tr>
    <td>push rA</td>
    <td colspan="8">52</td>
    <td colspan="5">rA</td>
    <td colspan="51">PADDING</td>
  </tr>
  <tr>
    <td>pop rA</td>
    <td colspan="8">53</td>
    <td colspan="5">rA</td>
    <td colspan="51">PADDING</td>
  </tr>
  <tr>
    <td>int DISP</td>
    <td colspan="8">59</td>
    <td colspan="8">DISPLACEMENT</td>
    <td colspan="48">PADDING</td>
  </tr>
  <tr>
    <td>call DEST</td>
    <td colspan="8">60</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jump DEST</td>
    <td colspan="8">61</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumpl DEST</td>
    <td colspan="8">62</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumple DEST</td>
    <td colspan="8">63</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumpg DEST</td>
    <td colspan="8">64</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumpge DEST</td>
    <td colspan="8">65</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumpe DEST</td>
    <td colspan="8">66</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>jumpne DEST</td>
    <td colspan="8">67</td>
    <td colspan="32">DESTINATION</td>
    <td colspan="24">PADDING</td>
  </tr>
  <tr>
    <td>ret</td>
    <td colspan="8">76</td>
    <td colspan="56">PADDING</td>
  </tr>
  <tr>
    <td>hlt</td>
    <td colspan="8">77</td>
    <td colspan="56">PADDING</td>
  </tr>
  <tr>
    <td>nop</td>
    <td colspan="8">78</td>
    <td colspan="56">PADDING</td>
  </tr>
  
</table>

<h6> 32 Registers Each 32-bits Wide </h6>

<table>
  <tr>
    <td>#</td>
    <td>Name</td>
  </tr>
  <tr>
    <td>0</td>
    <td>RIP</td>
  </tr>
  <tr>
    <td>1</td>
    <td>RSP</td>
  </tr>
  <tr>
    <td>2</td>
    <td>RBP</td>
  </tr>
  <tr>
    <td>3</td>
    <td>RCF</td>
  </tr>
  <tr>
    <td>4-31</td>
    <td>R4, R5, ..., R31</td>
  </tr>
</table>


