def subl1 : instruction :=
  definst "subl" $ do
    pattern fun (v_3224 : imm int) (v_3226 : reg (bv 32)) => do
      v_6368 <- eval (handleImmediateWithSignExtend v_3224 32 32);
      v_6372 <- getRegister v_3226;
      v_6374 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6368 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_6372));
      v_6375 <- eval (extract v_6374 1 33);
      v_6377 <- eval (isBitSet v_6374 1);
      v_6382 <- eval (eq (bv_xor (extract v_6368 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3226) v_6375;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6368 v_6372) 27) (isBitSet v_6374 28)));
      setRegister cf (notBool_ (isBitSet v_6374 0));
      setRegister of (bit_and (eq v_6382 (isBitSet v_6372 0)) (notBool_ (eq v_6382 v_6377)));
      setRegister pf (parityFlag (extract v_6374 25 33));
      setRegister sf v_6377;
      setRegister zf (zeroFlag v_6375);
      pure ()
    pat_end;
    pattern fun (v_3234 : reg (bv 32)) (v_3235 : reg (bv 32)) => do
      v_6406 <- getRegister v_3234;
      v_6410 <- getRegister v_3235;
      v_6412 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6406 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_6410));
      v_6413 <- eval (extract v_6412 1 33);
      v_6415 <- eval (isBitSet v_6412 1);
      v_6420 <- eval (eq (bv_xor (extract v_6406 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3235) v_6413;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6406 v_6410) 27) (isBitSet v_6412 28)));
      setRegister cf (notBool_ (isBitSet v_6412 0));
      setRegister of (bit_and (eq v_6420 (isBitSet v_6410 0)) (notBool_ (eq v_6420 v_6415)));
      setRegister pf (parityFlag (extract v_6412 25 33));
      setRegister sf v_6415;
      setRegister zf (zeroFlag v_6413);
      pure ()
    pat_end;
    pattern fun (v_3229 : Mem) (v_3230 : reg (bv 32)) => do
      v_9253 <- evaluateAddress v_3229;
      v_9254 <- load v_9253 4;
      v_9258 <- getRegister v_3230;
      v_9260 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9254 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_9258));
      v_9261 <- eval (extract v_9260 1 33);
      v_9263 <- eval (isBitSet v_9260 1);
      v_9268 <- eval (eq (bv_xor (extract v_9254 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3230) v_9261;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9254 v_9258) 27) (isBitSet v_9260 28)));
      setRegister cf (notBool_ (isBitSet v_9260 0));
      setRegister of (bit_and (eq v_9268 (isBitSet v_9258 0)) (notBool_ (eq v_9268 v_9263)));
      setRegister pf (parityFlag (extract v_9260 25 33));
      setRegister sf v_9263;
      setRegister zf (zeroFlag v_9261);
      pure ()
    pat_end;
    pattern fun (v_3217 : imm int) (v_3216 : Mem) => do
      v_10880 <- evaluateAddress v_3216;
      v_10881 <- eval (handleImmediateWithSignExtend v_3217 32 32);
      v_10885 <- load v_10880 4;
      v_10887 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10881 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_10885));
      v_10888 <- eval (extract v_10887 1 33);
      store v_10880 v_10888 4;
      v_10891 <- eval (isBitSet v_10887 1);
      v_10896 <- eval (eq (bv_xor (extract v_10881 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10881 v_10885) 27) (isBitSet v_10887 28)));
      setRegister cf (notBool_ (isBitSet v_10887 0));
      setRegister of (bit_and (eq v_10896 (isBitSet v_10885 0)) (notBool_ (eq v_10896 v_10891)));
      setRegister pf (parityFlag (extract v_10887 25 33));
      setRegister sf v_10891;
      setRegister zf (zeroFlag v_10888);
      pure ()
    pat_end;
    pattern fun (v_3221 : reg (bv 32)) (v_3220 : Mem) => do
      v_10915 <- evaluateAddress v_3220;
      v_10916 <- getRegister v_3221;
      v_10920 <- load v_10915 4;
      v_10922 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10916 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_10920));
      v_10923 <- eval (extract v_10922 1 33);
      store v_10915 v_10923 4;
      v_10926 <- eval (isBitSet v_10922 1);
      v_10931 <- eval (eq (bv_xor (extract v_10916 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10916 v_10920) 27) (isBitSet v_10922 28)));
      setRegister cf (notBool_ (isBitSet v_10922 0));
      setRegister of (bit_and (eq v_10931 (isBitSet v_10920 0)) (notBool_ (eq v_10931 v_10926)));
      setRegister pf (parityFlag (extract v_10922 25 33));
      setRegister sf v_10926;
      setRegister zf (zeroFlag v_10923);
      pure ()
    pat_end
