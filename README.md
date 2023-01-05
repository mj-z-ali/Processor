# Processor

This repository presents a functional, but soon-to-be fully-realized model of a 32-bit processor developed entirely from first principles. 
A finite-state automaton (FSA) was used to model the processor. Then, sequential logical expressions were derived from said automaton. 
The end goal of this project is a practical, formally verified, Turing complete processor built on an FPGA.

In this repository, you will find:

* [A Simulink file](https://github.com/Amjad-H-Ali/Processor/blob/main/PROCESSOR.slx) : Simulink is a MATLAB-based software for modeling and simulating systems. The interactive version of the FSA was designed in Simulink and looks like this:

<h6>Abstract overview of the FSA </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/PROC_MODEL_SIMULINK.png?raw=true)

<h6> Detailed FSA of the Multiplier </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/MULT_MODEL_SIMULINK.png?raw=true)

<h6> Detailed FSA of the Adder </h6>

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/ADDER_MODEL_SIMULINK.png?raw=true)


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


![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/MULT_MODEL_GRAFFLE.png?raw=true)

![MODEL](https://github.com/Amjad-H-Ali/Processor/blob/main/img/ADDER_MODEL_GRAFFLE.png?raw=true)
