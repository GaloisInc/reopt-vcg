def shlw1 : instruction :=
  definst "shlw" $ do
    pattern fun cl (v_2815 : reg (bv 16)) => do
      v_5219 <- getRegister rcx;
      v_5221 <- eval (bv_and (extract v_5219 56 64) (expression.bv_nat 8 31));
      v_5222 <- eval (uge v_5221 (expression.bv_nat 8 16));
      v_5225 <- eval (eq v_5221 (expression.bv_nat 8 0));
      v_5226 <- eval (notBool_ v_5225);
      v_5227 <- getRegister v_2815;
      v_5232 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5227) (uvalueMInt (concat (expression.bv_nat 9 0) v_5221))) 0 17);
      v_5236 <- getRegister cf;
      v_5241 <- eval (bit_or (bit_and v_5222 undef) (bit_and (notBool_ v_5222) (bit_or (bit_and v_5226 (eq (extract v_5232 0 1) (expression.bv_nat 1 1))) (bit_and v_5225 (eq v_5236 (expression.bv_nat 1 1))))));
      v_5244 <- eval (eq (extract v_5232 1 2) (expression.bv_nat 1 1));
      v_5246 <- getRegister sf;
      v_5251 <- eval (bit_and v_5226 undef);
      v_5252 <- getRegister af;
      v_5257 <- eval (extract v_5232 1 17);
      v_5260 <- getRegister zf;
      v_5295 <- getRegister pf;
      v_5300 <- eval (eq v_5221 (expression.bv_nat 8 1));
      v_5305 <- getRegister of;
      setRegister (lhs.of_reg v_2815) v_5257;
      setRegister of (mux (bit_or (bit_and v_5300 (notBool_ (eq v_5241 v_5244))) (bit_and (notBool_ v_5300) (bit_or v_5251 (bit_and v_5225 (eq v_5305 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5226 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5232 16 17) (expression.bv_nat 1 1)) (eq (extract v_5232 15 16) (expression.bv_nat 1 1)))) (eq (extract v_5232 14 15) (expression.bv_nat 1 1)))) (eq (extract v_5232 13 14) (expression.bv_nat 1 1)))) (eq (extract v_5232 12 13) (expression.bv_nat 1 1)))) (eq (extract v_5232 11 12) (expression.bv_nat 1 1)))) (eq (extract v_5232 10 11) (expression.bv_nat 1 1)))) (eq (extract v_5232 9 10) (expression.bv_nat 1 1)))) (bit_and v_5225 (eq v_5295 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5226 (eq v_5257 (expression.bv_nat 16 0))) (bit_and v_5225 (eq v_5260 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5251 (bit_and v_5225 (eq v_5252 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5226 v_5244) (bit_and v_5225 (eq v_5246 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5241 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2818 : imm int) (v_2820 : reg (bv 16)) => do
      v_5320 <- eval (bv_and (handleImmediateWithSignExtend v_2818 8 8) (expression.bv_nat 8 31));
      v_5321 <- eval (uge v_5320 (expression.bv_nat 8 16));
      v_5324 <- eval (eq v_5320 (expression.bv_nat 8 0));
      v_5325 <- eval (notBool_ v_5324);
      v_5326 <- getRegister v_2820;
      v_5331 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5326) (uvalueMInt (concat (expression.bv_nat 9 0) v_5320))) 0 17);
      v_5335 <- getRegister cf;
      v_5340 <- eval (bit_or (bit_and v_5321 undef) (bit_and (notBool_ v_5321) (bit_or (bit_and v_5325 (eq (extract v_5331 0 1) (expression.bv_nat 1 1))) (bit_and v_5324 (eq v_5335 (expression.bv_nat 1 1))))));
      v_5343 <- eval (eq (extract v_5331 1 2) (expression.bv_nat 1 1));
      v_5345 <- getRegister sf;
      v_5350 <- eval (bit_and v_5325 undef);
      v_5351 <- getRegister af;
      v_5356 <- eval (extract v_5331 1 17);
      v_5359 <- getRegister zf;
      v_5394 <- getRegister pf;
      v_5399 <- eval (eq v_5320 (expression.bv_nat 8 1));
      v_5404 <- getRegister of;
      setRegister (lhs.of_reg v_2820) v_5356;
      setRegister of (mux (bit_or (bit_and v_5399 (notBool_ (eq v_5340 v_5343))) (bit_and (notBool_ v_5399) (bit_or v_5350 (bit_and v_5324 (eq v_5404 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5325 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5331 16 17) (expression.bv_nat 1 1)) (eq (extract v_5331 15 16) (expression.bv_nat 1 1)))) (eq (extract v_5331 14 15) (expression.bv_nat 1 1)))) (eq (extract v_5331 13 14) (expression.bv_nat 1 1)))) (eq (extract v_5331 12 13) (expression.bv_nat 1 1)))) (eq (extract v_5331 11 12) (expression.bv_nat 1 1)))) (eq (extract v_5331 10 11) (expression.bv_nat 1 1)))) (eq (extract v_5331 9 10) (expression.bv_nat 1 1)))) (bit_and v_5324 (eq v_5394 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5325 (eq v_5356 (expression.bv_nat 16 0))) (bit_and v_5324 (eq v_5359 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5350 (bit_and v_5324 (eq v_5351 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5325 v_5343) (bit_and v_5324 (eq v_5345 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5340 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2824 : reg (bv 16)) => do
      v_5418 <- getRegister v_2824;
      v_5421 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5418) 1) 0 17);
      v_5422 <- eval (extract v_5421 0 1);
      v_5423 <- eval (extract v_5421 1 2);
      v_5424 <- eval (extract v_5421 1 17);
      setRegister (lhs.of_reg v_2824) v_5424;
      setRegister of (mux (notBool_ (eq (eq v_5422 (expression.bv_nat 1 1)) (eq v_5423 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5421 9 17));
      setRegister zf (zeroFlag v_5424);
      setRegister af undef;
      setRegister sf v_5423;
      setRegister cf v_5422;
      pure ()
    pat_end;
    pattern fun cl (v_2804 : Mem) => do
      v_11558 <- evaluateAddress v_2804;
      v_11559 <- load v_11558 2;
      v_11561 <- getRegister rcx;
      v_11563 <- eval (bv_and (extract v_11561 56 64) (expression.bv_nat 8 31));
      v_11567 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11559) (uvalueMInt (concat (expression.bv_nat 9 0) v_11563))) 0 17);
      v_11568 <- eval (extract v_11567 1 17);
      store v_11558 v_11568 2;
      v_11570 <- eval (uge v_11563 (expression.bv_nat 8 16));
      v_11573 <- eval (eq v_11563 (expression.bv_nat 8 0));
      v_11574 <- eval (notBool_ v_11573);
      v_11578 <- getRegister cf;
      v_11583 <- eval (bit_or (bit_and v_11570 undef) (bit_and (notBool_ v_11570) (bit_or (bit_and v_11574 (eq (extract v_11567 0 1) (expression.bv_nat 1 1))) (bit_and v_11573 (eq v_11578 (expression.bv_nat 1 1))))));
      v_11586 <- eval (eq (extract v_11567 1 2) (expression.bv_nat 1 1));
      v_11588 <- getRegister sf;
      v_11595 <- getRegister zf;
      v_11600 <- eval (bit_and v_11574 undef);
      v_11601 <- getRegister af;
      v_11636 <- getRegister pf;
      v_11641 <- eval (eq v_11563 (expression.bv_nat 8 1));
      v_11646 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11641 (notBool_ (eq v_11583 v_11586))) (bit_and (notBool_ v_11641) (bit_or v_11600 (bit_and v_11573 (eq v_11646 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11574 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11567 16 17) (expression.bv_nat 1 1)) (eq (extract v_11567 15 16) (expression.bv_nat 1 1)))) (eq (extract v_11567 14 15) (expression.bv_nat 1 1)))) (eq (extract v_11567 13 14) (expression.bv_nat 1 1)))) (eq (extract v_11567 12 13) (expression.bv_nat 1 1)))) (eq (extract v_11567 11 12) (expression.bv_nat 1 1)))) (eq (extract v_11567 10 11) (expression.bv_nat 1 1)))) (eq (extract v_11567 9 10) (expression.bv_nat 1 1)))) (bit_and v_11573 (eq v_11636 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11600 (bit_and v_11573 (eq v_11601 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11574 (eq v_11568 (expression.bv_nat 16 0))) (bit_and v_11573 (eq v_11595 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11574 v_11586) (bit_and v_11573 (eq v_11588 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11583 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2807 : imm int) (v_2808 : Mem) => do
      v_11659 <- evaluateAddress v_2808;
      v_11660 <- load v_11659 2;
      v_11663 <- eval (bv_and (handleImmediateWithSignExtend v_2807 8 8) (expression.bv_nat 8 31));
      v_11667 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11660) (uvalueMInt (concat (expression.bv_nat 9 0) v_11663))) 0 17);
      v_11668 <- eval (extract v_11667 1 17);
      store v_11659 v_11668 2;
      v_11670 <- eval (uge v_11663 (expression.bv_nat 8 16));
      v_11673 <- eval (eq v_11663 (expression.bv_nat 8 0));
      v_11674 <- eval (notBool_ v_11673);
      v_11678 <- getRegister cf;
      v_11683 <- eval (bit_or (bit_and v_11670 undef) (bit_and (notBool_ v_11670) (bit_or (bit_and v_11674 (eq (extract v_11667 0 1) (expression.bv_nat 1 1))) (bit_and v_11673 (eq v_11678 (expression.bv_nat 1 1))))));
      v_11686 <- eval (eq (extract v_11667 1 2) (expression.bv_nat 1 1));
      v_11688 <- getRegister sf;
      v_11695 <- getRegister zf;
      v_11700 <- eval (bit_and v_11674 undef);
      v_11701 <- getRegister af;
      v_11736 <- getRegister pf;
      v_11741 <- eval (eq v_11663 (expression.bv_nat 8 1));
      v_11746 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11741 (notBool_ (eq v_11683 v_11686))) (bit_and (notBool_ v_11741) (bit_or v_11700 (bit_and v_11673 (eq v_11746 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11674 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11667 16 17) (expression.bv_nat 1 1)) (eq (extract v_11667 15 16) (expression.bv_nat 1 1)))) (eq (extract v_11667 14 15) (expression.bv_nat 1 1)))) (eq (extract v_11667 13 14) (expression.bv_nat 1 1)))) (eq (extract v_11667 12 13) (expression.bv_nat 1 1)))) (eq (extract v_11667 11 12) (expression.bv_nat 1 1)))) (eq (extract v_11667 10 11) (expression.bv_nat 1 1)))) (eq (extract v_11667 9 10) (expression.bv_nat 1 1)))) (bit_and v_11673 (eq v_11736 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11700 (bit_and v_11673 (eq v_11701 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11674 (eq v_11668 (expression.bv_nat 16 0))) (bit_and v_11673 (eq v_11695 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11674 v_11686) (bit_and v_11673 (eq v_11688 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11683 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
