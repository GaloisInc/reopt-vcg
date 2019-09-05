def adcl1 : instruction :=
  definst "adcl" $ do
    pattern fun (v_2510 : imm int) (v_2511 : reg (bv 32)) => do
      v_4111 <- getRegister cf;
      v_4113 <- eval (handleImmediateWithSignExtend v_2510 32 32);
      v_4114 <- eval (concat (expression.bv_nat 1 0) v_4113);
      v_4117 <- getRegister v_2511;
      v_4119 <- eval (add (mux (eq v_4111 (expression.bv_nat 1 1)) (add v_4114 (expression.bv_nat 33 1)) v_4114) (concat (expression.bv_nat 1 0) v_4117));
      v_4120 <- eval (extract v_4119 1 33);
      v_4122 <- eval (isBitSet v_4119 1);
      v_4125 <- eval (isBitSet v_4113 0);
      setRegister (lhs.of_reg v_2511) v_4120;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4113 v_4117) 27) (isBitSet v_4119 28)));
      setRegister cf (isBitSet v_4119 0);
      setRegister of (bit_and (eq v_4125 (isBitSet v_4117 0)) (notBool_ (eq v_4125 v_4122)));
      setRegister pf (parityFlag (extract v_4119 25 33));
      setRegister sf v_4122;
      setRegister zf (zeroFlag v_4120);
      pure ()
    pat_end;
    pattern fun (v_2519 : reg (bv 32)) (v_2520 : reg (bv 32)) => do
      v_4148 <- getRegister cf;
      v_4150 <- getRegister v_2519;
      v_4151 <- eval (concat (expression.bv_nat 1 0) v_4150);
      v_4154 <- getRegister v_2520;
      v_4156 <- eval (add (mux (eq v_4148 (expression.bv_nat 1 1)) (add v_4151 (expression.bv_nat 33 1)) v_4151) (concat (expression.bv_nat 1 0) v_4154));
      v_4157 <- eval (extract v_4156 1 33);
      v_4159 <- eval (isBitSet v_4156 1);
      v_4162 <- eval (isBitSet v_4150 0);
      setRegister (lhs.of_reg v_2520) v_4157;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4150 v_4154) 27) (isBitSet v_4156 28)));
      setRegister cf (isBitSet v_4156 0);
      setRegister of (bit_and (eq v_4162 (isBitSet v_4154 0)) (notBool_ (eq v_4162 v_4159)));
      setRegister pf (parityFlag (extract v_4156 25 33));
      setRegister sf v_4159;
      setRegister zf (zeroFlag v_4157);
      pure ()
    pat_end;
    pattern fun (v_2516 : Mem) (v_2515 : reg (bv 32)) => do
      v_8717 <- getRegister cf;
      v_8719 <- evaluateAddress v_2516;
      v_8720 <- load v_8719 4;
      v_8721 <- eval (concat (expression.bv_nat 1 0) v_8720);
      v_8724 <- getRegister v_2515;
      v_8726 <- eval (add (mux (eq v_8717 (expression.bv_nat 1 1)) (add v_8721 (expression.bv_nat 33 1)) v_8721) (concat (expression.bv_nat 1 0) v_8724));
      v_8727 <- eval (extract v_8726 1 33);
      v_8729 <- eval (isBitSet v_8726 1);
      v_8732 <- eval (isBitSet v_8720 0);
      setRegister (lhs.of_reg v_2515) v_8727;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8720 v_8724) 27) (isBitSet v_8726 28)));
      setRegister cf (isBitSet v_8726 0);
      setRegister of (bit_and (eq v_8732 (isBitSet v_8724 0)) (notBool_ (eq v_8732 v_8729)));
      setRegister pf (parityFlag (extract v_8726 25 33));
      setRegister sf v_8729;
      setRegister zf (zeroFlag v_8727);
      pure ()
    pat_end;
    pattern fun (v_2502 : imm int) (v_2503 : Mem) => do
      v_10083 <- evaluateAddress v_2503;
      v_10084 <- getRegister cf;
      v_10086 <- eval (handleImmediateWithSignExtend v_2502 32 32);
      v_10087 <- eval (concat (expression.bv_nat 1 0) v_10086);
      v_10090 <- load v_10083 4;
      v_10092 <- eval (add (mux (eq v_10084 (expression.bv_nat 1 1)) (add v_10087 (expression.bv_nat 33 1)) v_10087) (concat (expression.bv_nat 1 0) v_10090));
      v_10093 <- eval (extract v_10092 1 33);
      store v_10083 v_10093 4;
      v_10096 <- eval (isBitSet v_10092 1);
      v_10099 <- eval (isBitSet v_10086 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10086 v_10090) 27) (isBitSet v_10092 28)));
      setRegister cf (isBitSet v_10092 0);
      setRegister of (bit_and (eq v_10099 (isBitSet v_10090 0)) (notBool_ (eq v_10099 v_10096)));
      setRegister pf (parityFlag (extract v_10092 25 33));
      setRegister sf v_10096;
      setRegister zf (zeroFlag v_10093);
      pure ()
    pat_end;
    pattern fun (v_2506 : reg (bv 32)) (v_2507 : Mem) => do
      v_10117 <- evaluateAddress v_2507;
      v_10118 <- getRegister cf;
      v_10120 <- getRegister v_2506;
      v_10121 <- eval (concat (expression.bv_nat 1 0) v_10120);
      v_10124 <- load v_10117 4;
      v_10126 <- eval (add (mux (eq v_10118 (expression.bv_nat 1 1)) (add v_10121 (expression.bv_nat 33 1)) v_10121) (concat (expression.bv_nat 1 0) v_10124));
      v_10127 <- eval (extract v_10126 1 33);
      store v_10117 v_10127 4;
      v_10130 <- eval (isBitSet v_10126 1);
      v_10133 <- eval (isBitSet v_10120 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10120 v_10124) 27) (isBitSet v_10126 28)));
      setRegister cf (isBitSet v_10126 0);
      setRegister of (bit_and (eq v_10133 (isBitSet v_10124 0)) (notBool_ (eq v_10133 v_10130)));
      setRegister pf (parityFlag (extract v_10126 25 33));
      setRegister sf v_10130;
      setRegister zf (zeroFlag v_10127);
      pure ()
    pat_end
