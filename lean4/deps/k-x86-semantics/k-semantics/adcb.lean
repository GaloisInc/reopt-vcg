def adcb1 : instruction :=
  definst "adcb" $ do
    pattern fun (v_2478 : imm int) (v_2481 : reg (bv 8)) => do
      v_3967 <- getRegister cf;
      v_3969 <- eval (handleImmediateWithSignExtend v_2478 8 8);
      v_3970 <- eval (concat (expression.bv_nat 1 0) v_3969);
      v_3973 <- getRegister v_2481;
      v_3975 <- eval (add (mux (eq v_3967 (expression.bv_nat 1 1)) (add v_3970 (expression.bv_nat 9 1)) v_3970) (concat (expression.bv_nat 1 0) v_3973));
      v_3976 <- eval (extract v_3975 1 9);
      v_3978 <- eval (isBitSet v_3975 1);
      v_3980 <- eval (isBitSet v_3969 0);
      setRegister (lhs.of_reg v_2481) v_3976;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3969 v_3973) 3) (isBitSet v_3975 4)));
      setRegister cf (isBitSet v_3975 0);
      setRegister of (bit_and (eq v_3980 (isBitSet v_3973 0)) (notBool_ (eq v_3980 v_3978)));
      setRegister pf (parityFlag v_3976);
      setRegister sf v_3978;
      setRegister zf (zeroFlag v_3976);
      pure ()
    pat_end;
    pattern fun (v_2494 : reg (bv 8)) (v_2495 : reg (bv 8)) => do
      v_4035 <- getRegister cf;
      v_4037 <- getRegister v_2494;
      v_4038 <- eval (concat (expression.bv_nat 1 0) v_4037);
      v_4041 <- getRegister v_2495;
      v_4043 <- eval (add (mux (eq v_4035 (expression.bv_nat 1 1)) (add v_4038 (expression.bv_nat 9 1)) v_4038) (concat (expression.bv_nat 1 0) v_4041));
      v_4044 <- eval (extract v_4043 1 9);
      v_4046 <- eval (isBitSet v_4043 1);
      v_4048 <- eval (isBitSet v_4037 0);
      setRegister (lhs.of_reg v_2495) v_4044;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4037 v_4041) 3) (isBitSet v_4043 4)));
      setRegister cf (isBitSet v_4043 0);
      setRegister of (bit_and (eq v_4048 (isBitSet v_4041 0)) (notBool_ (eq v_4048 v_4046)));
      setRegister pf (parityFlag v_4044);
      setRegister sf v_4046;
      setRegister zf (zeroFlag v_4044);
      pure ()
    pat_end;
    pattern fun (v_2484 : Mem) (v_2485 : reg (bv 8)) => do
      v_8682 <- getRegister cf;
      v_8684 <- evaluateAddress v_2484;
      v_8685 <- load v_8684 1;
      v_8686 <- eval (concat (expression.bv_nat 1 0) v_8685);
      v_8689 <- getRegister v_2485;
      v_8691 <- eval (add (mux (eq v_8682 (expression.bv_nat 1 1)) (add v_8686 (expression.bv_nat 9 1)) v_8686) (concat (expression.bv_nat 1 0) v_8689));
      v_8692 <- eval (extract v_8691 1 9);
      v_8694 <- eval (isBitSet v_8691 1);
      v_8696 <- eval (isBitSet v_8685 0);
      setRegister (lhs.of_reg v_2485) v_8692;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8685 v_8689) 3) (isBitSet v_8691 4)));
      setRegister cf (isBitSet v_8691 0);
      setRegister of (bit_and (eq v_8696 (isBitSet v_8689 0)) (notBool_ (eq v_8696 v_8694)));
      setRegister pf (parityFlag v_8692);
      setRegister sf v_8694;
      setRegister zf (zeroFlag v_8692);
      pure ()
    pat_end;
    pattern fun (v_2447 : imm int) (v_2449 : Mem) => do
      v_9984 <- evaluateAddress v_2449;
      v_9985 <- getRegister cf;
      v_9987 <- eval (handleImmediateWithSignExtend v_2447 8 8);
      v_9988 <- eval (concat (expression.bv_nat 1 0) v_9987);
      v_9991 <- load v_9984 1;
      v_9993 <- eval (add (mux (eq v_9985 (expression.bv_nat 1 1)) (add v_9988 (expression.bv_nat 9 1)) v_9988) (concat (expression.bv_nat 1 0) v_9991));
      v_9994 <- eval (extract v_9993 1 9);
      store v_9984 v_9994 1;
      v_9997 <- eval (isBitSet v_9993 1);
      v_9999 <- eval (isBitSet v_9987 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9987 v_9991) 3) (isBitSet v_9993 4)));
      setRegister cf (isBitSet v_9993 0);
      setRegister of (bit_and (eq v_9999 (isBitSet v_9991 0)) (notBool_ (eq v_9999 v_9997)));
      setRegister pf (parityFlag v_9994);
      setRegister sf v_9997;
      setRegister zf (zeroFlag v_9994);
      pure ()
    pat_end;
    pattern fun (v_2457 : reg (bv 8)) (v_2456 : Mem) => do
      v_10050 <- evaluateAddress v_2456;
      v_10051 <- getRegister cf;
      v_10053 <- getRegister v_2457;
      v_10054 <- eval (concat (expression.bv_nat 1 0) v_10053);
      v_10057 <- load v_10050 1;
      v_10059 <- eval (add (mux (eq v_10051 (expression.bv_nat 1 1)) (add v_10054 (expression.bv_nat 9 1)) v_10054) (concat (expression.bv_nat 1 0) v_10057));
      v_10060 <- eval (extract v_10059 1 9);
      store v_10050 v_10060 1;
      v_10063 <- eval (isBitSet v_10059 1);
      v_10065 <- eval (isBitSet v_10053 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10053 v_10057) 3) (isBitSet v_10059 4)));
      setRegister cf (isBitSet v_10059 0);
      setRegister of (bit_and (eq v_10065 (isBitSet v_10057 0)) (notBool_ (eq v_10065 v_10063)));
      setRegister pf (parityFlag v_10060);
      setRegister sf v_10063;
      setRegister zf (zeroFlag v_10060);
      pure ()
    pat_end
