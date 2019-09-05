def adcq1 : instruction :=
  definst "adcq" $ do
    pattern fun (v_2532 : imm int) (v_2534 : reg (bv 64)) => do
      v_4189 <- getRegister cf;
      v_4191 <- eval (handleImmediateWithSignExtend v_2532 32 32);
      v_4192 <- eval (sext v_4191 64);
      v_4193 <- eval (concat (expression.bv_nat 1 0) v_4192);
      v_4196 <- getRegister v_2534;
      v_4198 <- eval (add (mux (eq v_4189 (expression.bv_nat 1 1)) (add v_4193 (expression.bv_nat 65 1)) v_4193) (concat (expression.bv_nat 1 0) v_4196));
      v_4199 <- eval (extract v_4198 1 65);
      v_4201 <- eval (isBitSet v_4198 1);
      v_4204 <- eval (isBitSet v_4192 0);
      setRegister (lhs.of_reg v_2534) v_4199;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4191 27) (isBitSet v_4196 59))) (isBitSet v_4198 60)));
      setRegister cf (isBitSet v_4198 0);
      setRegister of (bit_and (eq v_4204 (isBitSet v_4196 0)) (notBool_ (eq v_4204 v_4201)));
      setRegister pf (parityFlag (extract v_4198 57 65));
      setRegister sf v_4201;
      setRegister zf (zeroFlag v_4199);
      pure ()
    pat_end;
    pattern fun (v_2542 : reg (bv 64)) (v_2543 : reg (bv 64)) => do
      v_4229 <- getRegister cf;
      v_4231 <- getRegister v_2542;
      v_4232 <- eval (concat (expression.bv_nat 1 0) v_4231);
      v_4235 <- getRegister v_2543;
      v_4237 <- eval (add (mux (eq v_4229 (expression.bv_nat 1 1)) (add v_4232 (expression.bv_nat 65 1)) v_4232) (concat (expression.bv_nat 1 0) v_4235));
      v_4238 <- eval (extract v_4237 1 65);
      v_4240 <- eval (isBitSet v_4237 1);
      v_4243 <- eval (isBitSet v_4231 0);
      setRegister (lhs.of_reg v_2543) v_4238;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4231 v_4235) 59) (isBitSet v_4237 60)));
      setRegister cf (isBitSet v_4237 0);
      setRegister of (bit_and (eq v_4243 (isBitSet v_4235 0)) (notBool_ (eq v_4243 v_4240)));
      setRegister pf (parityFlag (extract v_4237 57 65));
      setRegister sf v_4240;
      setRegister zf (zeroFlag v_4238);
      pure ()
    pat_end;
    pattern fun (v_2537 : Mem) (v_2538 : reg (bv 64)) => do
      v_8753 <- getRegister cf;
      v_8755 <- evaluateAddress v_2537;
      v_8756 <- load v_8755 8;
      v_8757 <- eval (concat (expression.bv_nat 1 0) v_8756);
      v_8760 <- getRegister v_2538;
      v_8762 <- eval (add (mux (eq v_8753 (expression.bv_nat 1 1)) (add v_8757 (expression.bv_nat 65 1)) v_8757) (concat (expression.bv_nat 1 0) v_8760));
      v_8763 <- eval (extract v_8762 1 65);
      v_8765 <- eval (isBitSet v_8762 1);
      v_8768 <- eval (isBitSet v_8756 0);
      setRegister (lhs.of_reg v_2538) v_8763;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8756 v_8760) 59) (isBitSet v_8762 60)));
      setRegister cf (isBitSet v_8762 0);
      setRegister of (bit_and (eq v_8768 (isBitSet v_8760 0)) (notBool_ (eq v_8768 v_8765)));
      setRegister pf (parityFlag (extract v_8762 57 65));
      setRegister sf v_8765;
      setRegister zf (zeroFlag v_8763);
      pure ()
    pat_end;
    pattern fun (v_2524 : imm int) (v_2525 : Mem) => do
      v_10151 <- evaluateAddress v_2525;
      v_10152 <- getRegister cf;
      v_10154 <- eval (handleImmediateWithSignExtend v_2524 32 32);
      v_10155 <- eval (sext v_10154 64);
      v_10156 <- eval (concat (expression.bv_nat 1 0) v_10155);
      v_10159 <- load v_10151 8;
      v_10161 <- eval (add (mux (eq v_10152 (expression.bv_nat 1 1)) (add v_10156 (expression.bv_nat 65 1)) v_10156) (concat (expression.bv_nat 1 0) v_10159));
      v_10162 <- eval (extract v_10161 1 65);
      store v_10151 v_10162 8;
      v_10165 <- eval (isBitSet v_10161 1);
      v_10168 <- eval (isBitSet v_10155 0);
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_10154 27) (isBitSet v_10159 59))) (isBitSet v_10161 60)));
      setRegister cf (isBitSet v_10161 0);
      setRegister of (bit_and (eq v_10168 (isBitSet v_10159 0)) (notBool_ (eq v_10168 v_10165)));
      setRegister pf (parityFlag (extract v_10161 57 65));
      setRegister sf v_10165;
      setRegister zf (zeroFlag v_10162);
      pure ()
    pat_end;
    pattern fun (v_2529 : reg (bv 64)) (v_2528 : Mem) => do
      v_10188 <- evaluateAddress v_2528;
      v_10189 <- getRegister cf;
      v_10191 <- getRegister v_2529;
      v_10192 <- eval (concat (expression.bv_nat 1 0) v_10191);
      v_10195 <- load v_10188 8;
      v_10197 <- eval (add (mux (eq v_10189 (expression.bv_nat 1 1)) (add v_10192 (expression.bv_nat 65 1)) v_10192) (concat (expression.bv_nat 1 0) v_10195));
      v_10198 <- eval (extract v_10197 1 65);
      store v_10188 v_10198 8;
      v_10201 <- eval (isBitSet v_10197 1);
      v_10204 <- eval (isBitSet v_10191 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10191 v_10195) 59) (isBitSet v_10197 60)));
      setRegister cf (isBitSet v_10197 0);
      setRegister of (bit_and (eq v_10204 (isBitSet v_10195 0)) (notBool_ (eq v_10204 v_10201)));
      setRegister pf (parityFlag (extract v_10197 57 65));
      setRegister sf v_10201;
      setRegister zf (zeroFlag v_10198);
      pure ()
    pat_end
