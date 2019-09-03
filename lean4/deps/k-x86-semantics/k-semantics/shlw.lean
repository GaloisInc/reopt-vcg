def shlw1 : instruction :=
  definst "shlw" $ do
    pattern fun cl (v_2802 : reg (bv 16)) => do
      v_5218 <- getRegister rcx;
      v_5220 <- eval (bv_and (extract v_5218 56 64) (expression.bv_nat 8 31));
      v_5221 <- eval (uge v_5220 (expression.bv_nat 8 16));
      v_5224 <- eval (eq v_5220 (expression.bv_nat 8 0));
      v_5225 <- eval (notBool_ v_5224);
      v_5226 <- getRegister v_2802;
      v_5227 <- eval (concat (expression.bv_nat 1 0) v_5226);
      v_5232 <- eval (extract (shl v_5227 (uvalueMInt (concat (expression.bv_nat 9 0) v_5220))) 0 (bitwidthMInt v_5227));
      v_5236 <- getRegister cf;
      v_5241 <- eval (bit_or (bit_and v_5221 undef) (bit_and (notBool_ v_5221) (bit_or (bit_and v_5225 (eq (extract v_5232 0 1) (expression.bv_nat 1 1))) (bit_and v_5224 (eq v_5236 (expression.bv_nat 1 1))))));
      v_5244 <- eval (eq (extract v_5232 1 2) (expression.bv_nat 1 1));
      v_5246 <- getRegister sf;
      v_5251 <- eval (bit_and v_5225 undef);
      v_5252 <- getRegister af;
      v_5257 <- eval (extract v_5232 1 17);
      v_5260 <- getRegister zf;
      v_5295 <- getRegister pf;
      v_5300 <- eval (eq v_5220 (expression.bv_nat 8 1));
      v_5305 <- getRegister of;
      setRegister (lhs.of_reg v_2802) v_5257;
      setRegister of (mux (bit_or (bit_and v_5300 (notBool_ (eq v_5241 v_5244))) (bit_and (notBool_ v_5300) (bit_or v_5251 (bit_and v_5224 (eq v_5305 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5225 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5232 16 17) (expression.bv_nat 1 1)) (eq (extract v_5232 15 16) (expression.bv_nat 1 1)))) (eq (extract v_5232 14 15) (expression.bv_nat 1 1)))) (eq (extract v_5232 13 14) (expression.bv_nat 1 1)))) (eq (extract v_5232 12 13) (expression.bv_nat 1 1)))) (eq (extract v_5232 11 12) (expression.bv_nat 1 1)))) (eq (extract v_5232 10 11) (expression.bv_nat 1 1)))) (eq (extract v_5232 9 10) (expression.bv_nat 1 1)))) (bit_and v_5224 (eq v_5295 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5225 (eq v_5257 (expression.bv_nat 16 0))) (bit_and v_5224 (eq v_5260 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5251 (bit_and v_5224 (eq v_5252 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5225 v_5244) (bit_and v_5224 (eq v_5246 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5241 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2805 : imm int) (v_2807 : reg (bv 16)) => do
      v_5320 <- eval (bv_and (handleImmediateWithSignExtend v_2805 8 8) (expression.bv_nat 8 31));
      v_5321 <- eval (uge v_5320 (expression.bv_nat 8 16));
      v_5324 <- eval (eq v_5320 (expression.bv_nat 8 0));
      v_5325 <- eval (notBool_ v_5324);
      v_5326 <- getRegister v_2807;
      v_5327 <- eval (concat (expression.bv_nat 1 0) v_5326);
      v_5332 <- eval (extract (shl v_5327 (uvalueMInt (concat (expression.bv_nat 9 0) v_5320))) 0 (bitwidthMInt v_5327));
      v_5336 <- getRegister cf;
      v_5341 <- eval (bit_or (bit_and v_5321 undef) (bit_and (notBool_ v_5321) (bit_or (bit_and v_5325 (eq (extract v_5332 0 1) (expression.bv_nat 1 1))) (bit_and v_5324 (eq v_5336 (expression.bv_nat 1 1))))));
      v_5344 <- eval (eq (extract v_5332 1 2) (expression.bv_nat 1 1));
      v_5346 <- getRegister sf;
      v_5351 <- eval (bit_and v_5325 undef);
      v_5352 <- getRegister af;
      v_5357 <- eval (extract v_5332 1 17);
      v_5360 <- getRegister zf;
      v_5395 <- getRegister pf;
      v_5400 <- eval (eq v_5320 (expression.bv_nat 8 1));
      v_5405 <- getRegister of;
      setRegister (lhs.of_reg v_2807) v_5357;
      setRegister of (mux (bit_or (bit_and v_5400 (notBool_ (eq v_5341 v_5344))) (bit_and (notBool_ v_5400) (bit_or v_5351 (bit_and v_5324 (eq v_5405 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5325 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5332 16 17) (expression.bv_nat 1 1)) (eq (extract v_5332 15 16) (expression.bv_nat 1 1)))) (eq (extract v_5332 14 15) (expression.bv_nat 1 1)))) (eq (extract v_5332 13 14) (expression.bv_nat 1 1)))) (eq (extract v_5332 12 13) (expression.bv_nat 1 1)))) (eq (extract v_5332 11 12) (expression.bv_nat 1 1)))) (eq (extract v_5332 10 11) (expression.bv_nat 1 1)))) (eq (extract v_5332 9 10) (expression.bv_nat 1 1)))) (bit_and v_5324 (eq v_5395 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5325 (eq v_5357 (expression.bv_nat 16 0))) (bit_and v_5324 (eq v_5360 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5351 (bit_and v_5324 (eq v_5352 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5325 v_5344) (bit_and v_5324 (eq v_5346 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5341 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2811 : reg (bv 16)) => do
      v_5419 <- getRegister v_2811;
      v_5420 <- eval (concat (expression.bv_nat 1 0) v_5419);
      v_5423 <- eval (extract (shl v_5420 1) 0 (bitwidthMInt v_5420));
      v_5424 <- eval (extract v_5423 0 1);
      v_5425 <- eval (extract v_5423 1 2);
      v_5426 <- eval (extract v_5423 1 17);
      setRegister (lhs.of_reg v_2811) v_5426;
      setRegister of (mux (notBool_ (eq (eq v_5424 (expression.bv_nat 1 1)) (eq v_5425 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5423 9 17));
      setRegister zf (zeroFlag v_5426);
      setRegister af undef;
      setRegister sf v_5425;
      setRegister cf v_5424;
      pure ()
    pat_end;
    pattern fun cl (v_2791 : Mem) => do
      v_11478 <- evaluateAddress v_2791;
      v_11479 <- load v_11478 2;
      v_11480 <- eval (concat (expression.bv_nat 1 0) v_11479);
      v_11481 <- getRegister rcx;
      v_11483 <- eval (bv_and (extract v_11481 56 64) (expression.bv_nat 8 31));
      v_11488 <- eval (extract (shl v_11480 (uvalueMInt (concat (expression.bv_nat 9 0) v_11483))) 0 (bitwidthMInt v_11480));
      v_11489 <- eval (extract v_11488 1 17);
      store v_11478 v_11489 2;
      v_11491 <- eval (uge v_11483 (expression.bv_nat 8 16));
      v_11494 <- eval (eq v_11483 (expression.bv_nat 8 0));
      v_11495 <- eval (notBool_ v_11494);
      v_11499 <- getRegister cf;
      v_11504 <- eval (bit_or (bit_and v_11491 undef) (bit_and (notBool_ v_11491) (bit_or (bit_and v_11495 (eq (extract v_11488 0 1) (expression.bv_nat 1 1))) (bit_and v_11494 (eq v_11499 (expression.bv_nat 1 1))))));
      v_11507 <- eval (eq (extract v_11488 1 2) (expression.bv_nat 1 1));
      v_11509 <- getRegister sf;
      v_11516 <- getRegister zf;
      v_11521 <- eval (bit_and v_11495 undef);
      v_11522 <- getRegister af;
      v_11557 <- getRegister pf;
      v_11562 <- eval (eq v_11483 (expression.bv_nat 8 1));
      v_11567 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11562 (notBool_ (eq v_11504 v_11507))) (bit_and (notBool_ v_11562) (bit_or v_11521 (bit_and v_11494 (eq v_11567 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11495 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11488 16 17) (expression.bv_nat 1 1)) (eq (extract v_11488 15 16) (expression.bv_nat 1 1)))) (eq (extract v_11488 14 15) (expression.bv_nat 1 1)))) (eq (extract v_11488 13 14) (expression.bv_nat 1 1)))) (eq (extract v_11488 12 13) (expression.bv_nat 1 1)))) (eq (extract v_11488 11 12) (expression.bv_nat 1 1)))) (eq (extract v_11488 10 11) (expression.bv_nat 1 1)))) (eq (extract v_11488 9 10) (expression.bv_nat 1 1)))) (bit_and v_11494 (eq v_11557 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11521 (bit_and v_11494 (eq v_11522 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11495 (eq v_11489 (expression.bv_nat 16 0))) (bit_and v_11494 (eq v_11516 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11495 v_11507) (bit_and v_11494 (eq v_11509 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11504 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2794 : imm int) (v_2795 : Mem) => do
      v_11580 <- evaluateAddress v_2795;
      v_11581 <- load v_11580 2;
      v_11582 <- eval (concat (expression.bv_nat 1 0) v_11581);
      v_11584 <- eval (bv_and (handleImmediateWithSignExtend v_2794 8 8) (expression.bv_nat 8 31));
      v_11589 <- eval (extract (shl v_11582 (uvalueMInt (concat (expression.bv_nat 9 0) v_11584))) 0 (bitwidthMInt v_11582));
      v_11590 <- eval (extract v_11589 1 17);
      store v_11580 v_11590 2;
      v_11592 <- eval (uge v_11584 (expression.bv_nat 8 16));
      v_11595 <- eval (eq v_11584 (expression.bv_nat 8 0));
      v_11596 <- eval (notBool_ v_11595);
      v_11600 <- getRegister cf;
      v_11605 <- eval (bit_or (bit_and v_11592 undef) (bit_and (notBool_ v_11592) (bit_or (bit_and v_11596 (eq (extract v_11589 0 1) (expression.bv_nat 1 1))) (bit_and v_11595 (eq v_11600 (expression.bv_nat 1 1))))));
      v_11608 <- eval (eq (extract v_11589 1 2) (expression.bv_nat 1 1));
      v_11610 <- getRegister sf;
      v_11617 <- getRegister zf;
      v_11622 <- eval (bit_and v_11596 undef);
      v_11623 <- getRegister af;
      v_11658 <- getRegister pf;
      v_11663 <- eval (eq v_11584 (expression.bv_nat 8 1));
      v_11668 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11663 (notBool_ (eq v_11605 v_11608))) (bit_and (notBool_ v_11663) (bit_or v_11622 (bit_and v_11595 (eq v_11668 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11596 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11589 16 17) (expression.bv_nat 1 1)) (eq (extract v_11589 15 16) (expression.bv_nat 1 1)))) (eq (extract v_11589 14 15) (expression.bv_nat 1 1)))) (eq (extract v_11589 13 14) (expression.bv_nat 1 1)))) (eq (extract v_11589 12 13) (expression.bv_nat 1 1)))) (eq (extract v_11589 11 12) (expression.bv_nat 1 1)))) (eq (extract v_11589 10 11) (expression.bv_nat 1 1)))) (eq (extract v_11589 9 10) (expression.bv_nat 1 1)))) (bit_and v_11595 (eq v_11658 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11622 (bit_and v_11595 (eq v_11623 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11596 (eq v_11590 (expression.bv_nat 16 0))) (bit_and v_11595 (eq v_11617 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11596 v_11608) (bit_and v_11595 (eq v_11610 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11605 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
