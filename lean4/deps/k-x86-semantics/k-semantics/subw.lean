def subw1 : instruction :=
  definst "subw" $ do
    pattern fun (v_3312 : imm int) (v_3314 : reg (bv 16)) => do
      v_6691 <- eval (handleImmediateWithSignExtend v_3312 16 16);
      v_6695 <- getRegister v_3314;
      v_6697 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6691 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_6695));
      v_6698 <- eval (extract v_6697 1 17);
      v_6700 <- eval (isBitSet v_6697 1);
      v_6705 <- eval (eq (bv_xor (extract v_6691 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3314) v_6698;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6691 v_6695) 11) (isBitSet v_6697 12)));
      setRegister cf (notBool_ (isBitSet v_6697 0));
      setRegister of (bit_and (eq v_6705 (isBitSet v_6695 0)) (notBool_ (eq v_6705 v_6700)));
      setRegister pf (parityFlag (extract v_6697 9 17));
      setRegister sf v_6700;
      setRegister zf (zeroFlag v_6698);
      pure ()
    pat_end;
    pattern fun (v_3322 : reg (bv 16)) (v_3323 : reg (bv 16)) => do
      v_6729 <- getRegister v_3322;
      v_6733 <- getRegister v_3323;
      v_6735 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6729 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_6733));
      v_6736 <- eval (extract v_6735 1 17);
      v_6738 <- eval (isBitSet v_6735 1);
      v_6743 <- eval (eq (bv_xor (extract v_6729 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3323) v_6736;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6729 v_6733) 11) (isBitSet v_6735 12)));
      setRegister cf (notBool_ (isBitSet v_6735 0));
      setRegister of (bit_and (eq v_6743 (isBitSet v_6733 0)) (notBool_ (eq v_6743 v_6738)));
      setRegister pf (parityFlag (extract v_6735 9 17));
      setRegister sf v_6738;
      setRegister zf (zeroFlag v_6736);
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3318 : reg (bv 16)) => do
      v_9397 <- evaluateAddress v_3317;
      v_9398 <- load v_9397 2;
      v_9402 <- getRegister v_3318;
      v_9404 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9398 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_9402));
      v_9405 <- eval (extract v_9404 1 17);
      v_9407 <- eval (isBitSet v_9404 1);
      v_9412 <- eval (eq (bv_xor (extract v_9398 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3318) v_9405;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9398 v_9402) 11) (isBitSet v_9404 12)));
      setRegister cf (notBool_ (isBitSet v_9404 0));
      setRegister of (bit_and (eq v_9412 (isBitSet v_9402 0)) (notBool_ (eq v_9412 v_9407)));
      setRegister pf (parityFlag (extract v_9404 9 17));
      setRegister sf v_9407;
      setRegister zf (zeroFlag v_9405);
      pure ()
    pat_end;
    pattern fun (v_3305 : imm int) (v_3304 : Mem) => do
      v_11023 <- evaluateAddress v_3304;
      v_11024 <- eval (handleImmediateWithSignExtend v_3305 16 16);
      v_11028 <- load v_11023 2;
      v_11030 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_11024 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_11028));
      v_11031 <- eval (extract v_11030 1 17);
      store v_11023 v_11031 2;
      v_11034 <- eval (isBitSet v_11030 1);
      v_11039 <- eval (eq (bv_xor (extract v_11024 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11024 v_11028) 11) (isBitSet v_11030 12)));
      setRegister cf (notBool_ (isBitSet v_11030 0));
      setRegister of (bit_and (eq v_11039 (isBitSet v_11028 0)) (notBool_ (eq v_11039 v_11034)));
      setRegister pf (parityFlag (extract v_11030 9 17));
      setRegister sf v_11034;
      setRegister zf (zeroFlag v_11031);
      pure ()
    pat_end;
    pattern fun (v_3309 : reg (bv 16)) (v_3308 : Mem) => do
      v_11058 <- evaluateAddress v_3308;
      v_11059 <- getRegister v_3309;
      v_11063 <- load v_11058 2;
      v_11065 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_11059 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_11063));
      v_11066 <- eval (extract v_11065 1 17);
      store v_11058 v_11066 2;
      v_11069 <- eval (isBitSet v_11065 1);
      v_11074 <- eval (eq (bv_xor (extract v_11059 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11059 v_11063) 11) (isBitSet v_11065 12)));
      setRegister cf (notBool_ (isBitSet v_11065 0));
      setRegister of (bit_and (eq v_11074 (isBitSet v_11063 0)) (notBool_ (eq v_11074 v_11069)));
      setRegister pf (parityFlag (extract v_11065 9 17));
      setRegister sf v_11069;
      setRegister zf (zeroFlag v_11066);
      pure ()
    pat_end
