def subw1 : instruction :=
  definst "subw" $ do
    pattern fun (v_3340 : imm int) (v_3341 : reg (bv 16)) => do
      v_6132 <- eval (handleImmediateWithSignExtend v_3340 16 16);
      v_6136 <- getRegister v_3341;
      v_6138 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6132 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_6136));
      v_6139 <- eval (extract v_6138 1 17);
      v_6141 <- eval (isBitSet v_6138 1);
      v_6146 <- eval (eq (bv_xor (extract v_6132 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3341) v_6139;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6132 v_6136) 11) (isBitSet v_6138 12)));
      setRegister cf (isBitClear v_6138 0);
      setRegister of (bit_and (eq v_6146 (isBitSet v_6136 0)) (notBool_ (eq v_6146 v_6141)));
      setRegister pf (parityFlag (extract v_6138 9 17));
      setRegister sf v_6141;
      setRegister zf (zeroFlag v_6139);
      pure ()
    pat_end;
    pattern fun (v_3349 : reg (bv 16)) (v_3350 : reg (bv 16)) => do
      v_6169 <- getRegister v_3349;
      v_6173 <- getRegister v_3350;
      v_6175 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6169 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_6173));
      v_6176 <- eval (extract v_6175 1 17);
      v_6178 <- eval (isBitSet v_6175 1);
      v_6183 <- eval (eq (bv_xor (extract v_6169 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3350) v_6176;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6169 v_6173) 11) (isBitSet v_6175 12)));
      setRegister cf (isBitClear v_6175 0);
      setRegister of (bit_and (eq v_6183 (isBitSet v_6173 0)) (notBool_ (eq v_6183 v_6178)));
      setRegister pf (parityFlag (extract v_6175 9 17));
      setRegister sf v_6178;
      setRegister zf (zeroFlag v_6176);
      pure ()
    pat_end;
    pattern fun (v_3345 : Mem) (v_3346 : reg (bv 16)) => do
      v_8786 <- evaluateAddress v_3345;
      v_8787 <- load v_8786 2;
      v_8791 <- getRegister v_3346;
      v_8793 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8787 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_8791));
      v_8794 <- eval (extract v_8793 1 17);
      v_8796 <- eval (isBitSet v_8793 1);
      v_8801 <- eval (eq (bv_xor (extract v_8787 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3346) v_8794;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8787 v_8791) 11) (isBitSet v_8793 12)));
      setRegister cf (isBitClear v_8793 0);
      setRegister of (bit_and (eq v_8801 (isBitSet v_8791 0)) (notBool_ (eq v_8801 v_8796)));
      setRegister pf (parityFlag (extract v_8793 9 17));
      setRegister sf v_8796;
      setRegister zf (zeroFlag v_8794);
      pure ()
    pat_end;
    pattern fun (v_3333 : imm int) (v_3332 : Mem) => do
      v_10020 <- evaluateAddress v_3332;
      v_10021 <- eval (handleImmediateWithSignExtend v_3333 16 16);
      v_10025 <- load v_10020 2;
      v_10027 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10021 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_10025));
      v_10028 <- eval (extract v_10027 1 17);
      store v_10020 v_10028 2;
      v_10031 <- eval (isBitSet v_10027 1);
      v_10036 <- eval (eq (bv_xor (extract v_10021 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10021 v_10025) 11) (isBitSet v_10027 12)));
      setRegister cf (isBitClear v_10027 0);
      setRegister of (bit_and (eq v_10036 (isBitSet v_10025 0)) (notBool_ (eq v_10036 v_10031)));
      setRegister pf (parityFlag (extract v_10027 9 17));
      setRegister sf v_10031;
      setRegister zf (zeroFlag v_10028);
      pure ()
    pat_end;
    pattern fun (v_3337 : reg (bv 16)) (v_3336 : Mem) => do
      v_10054 <- evaluateAddress v_3336;
      v_10055 <- getRegister v_3337;
      v_10059 <- load v_10054 2;
      v_10061 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10055 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_10059));
      v_10062 <- eval (extract v_10061 1 17);
      store v_10054 v_10062 2;
      v_10065 <- eval (isBitSet v_10061 1);
      v_10070 <- eval (eq (bv_xor (extract v_10055 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10055 v_10059) 11) (isBitSet v_10061 12)));
      setRegister cf (isBitClear v_10061 0);
      setRegister of (bit_and (eq v_10070 (isBitSet v_10059 0)) (notBool_ (eq v_10070 v_10065)));
      setRegister pf (parityFlag (extract v_10061 9 17));
      setRegister sf v_10065;
      setRegister zf (zeroFlag v_10062);
      pure ()
    pat_end
