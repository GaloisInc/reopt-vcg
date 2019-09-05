def sall1 : instruction :=
  definst "sall" $ do
    pattern fun cl (v_2989 : reg (bv 32)) => do
      v_5917 <- getRegister rcx;
      v_5919 <- eval (bv_and (extract v_5917 56 64) (expression.bv_nat 8 31));
      v_5920 <- eval (eq v_5919 (expression.bv_nat 8 0));
      v_5921 <- eval (notBool_ v_5920);
      v_5922 <- getRegister v_2989;
      v_5926 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5922) (concat (expression.bv_nat 25 0) v_5919)) 0 33);
      v_5927 <- eval (extract v_5926 1 33);
      v_5930 <- getRegister zf;
      v_5934 <- eval (isBitSet v_5926 1);
      v_5936 <- getRegister sf;
      v_5943 <- getRegister pf;
      v_5947 <- eval (eq v_5919 (expression.bv_nat 8 1));
      v_5948 <- eval (uge v_5919 (expression.bv_nat 8 32));
      v_5953 <- getRegister cf;
      v_5958 <- eval (bit_or (bit_and v_5948 undef) (bit_and (notBool_ v_5948) (bit_or (bit_and v_5921 (isBitSet v_5926 0)) (bit_and v_5920 (eq v_5953 (expression.bv_nat 1 1))))));
      v_5963 <- eval (bit_and v_5921 undef);
      v_5964 <- getRegister of;
      v_5970 <- getRegister af;
      setRegister (lhs.of_reg v_2989) v_5927;
      setRegister af (bit_or v_5963 (bit_and v_5920 (eq v_5970 (expression.bv_nat 1 1))));
      setRegister cf v_5958;
      setRegister of (bit_or (bit_and v_5947 (notBool_ (eq v_5958 v_5934))) (bit_and (notBool_ v_5947) (bit_or v_5963 (bit_and v_5920 (eq v_5964 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5921 (parityFlag (extract v_5926 25 33))) (bit_and v_5920 (eq v_5943 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5921 v_5934) (bit_and v_5920 (eq v_5936 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5921 (eq v_5927 (expression.bv_nat 32 0))) (bit_and v_5920 (eq v_5930 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2992 : imm int) (v_2994 : reg (bv 32)) => do
      v_5982 <- eval (bv_and (handleImmediateWithSignExtend v_2992 8 8) (expression.bv_nat 8 31));
      v_5983 <- eval (eq v_5982 (expression.bv_nat 8 0));
      v_5984 <- eval (notBool_ v_5983);
      v_5985 <- getRegister v_2994;
      v_5989 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5985) (concat (expression.bv_nat 25 0) v_5982)) 0 33);
      v_5990 <- eval (extract v_5989 1 33);
      v_5993 <- getRegister zf;
      v_5997 <- eval (isBitSet v_5989 1);
      v_5999 <- getRegister sf;
      v_6006 <- getRegister pf;
      v_6010 <- eval (eq v_5982 (expression.bv_nat 8 1));
      v_6011 <- eval (uge v_5982 (expression.bv_nat 8 32));
      v_6016 <- getRegister cf;
      v_6021 <- eval (bit_or (bit_and v_6011 undef) (bit_and (notBool_ v_6011) (bit_or (bit_and v_5984 (isBitSet v_5989 0)) (bit_and v_5983 (eq v_6016 (expression.bv_nat 1 1))))));
      v_6026 <- eval (bit_and v_5984 undef);
      v_6027 <- getRegister of;
      v_6033 <- getRegister af;
      setRegister (lhs.of_reg v_2994) v_5990;
      setRegister af (bit_or v_6026 (bit_and v_5983 (eq v_6033 (expression.bv_nat 1 1))));
      setRegister cf v_6021;
      setRegister of (bit_or (bit_and v_6010 (notBool_ (eq v_6021 v_5997))) (bit_and (notBool_ v_6010) (bit_or v_6026 (bit_and v_5983 (eq v_6027 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5984 (parityFlag (extract v_5989 25 33))) (bit_and v_5983 (eq v_6006 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5984 v_5997) (bit_and v_5983 (eq v_5999 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5984 (eq v_5990 (expression.bv_nat 32 0))) (bit_and v_5983 (eq v_5993 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2997 : reg (bv 32)) => do
      v_8265 <- getRegister v_2997;
      v_8268 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8265) (expression.bv_nat 33 1)) 0 33);
      v_8269 <- eval (extract v_8268 1 33);
      v_8271 <- eval (isBitSet v_8268 1);
      v_8274 <- eval (isBitSet v_8268 0);
      setRegister (lhs.of_reg v_2997) v_8269;
      setRegister af undef;
      setRegister cf v_8274;
      setRegister of (notBool_ (eq v_8274 v_8271));
      setRegister pf (parityFlag (extract v_8268 25 33));
      setRegister sf v_8271;
      setRegister zf (zeroFlag v_8269);
      pure ()
    pat_end;
    pattern fun cl (v_2975 : Mem) => do
      v_13045 <- evaluateAddress v_2975;
      v_13046 <- load v_13045 4;
      v_13048 <- getRegister rcx;
      v_13050 <- eval (bv_and (extract v_13048 56 64) (expression.bv_nat 8 31));
      v_13053 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13046) (concat (expression.bv_nat 25 0) v_13050)) 0 33);
      v_13054 <- eval (extract v_13053 1 33);
      store v_13045 v_13054 4;
      v_13056 <- eval (eq v_13050 (expression.bv_nat 8 0));
      v_13057 <- eval (notBool_ v_13056);
      v_13060 <- getRegister zf;
      v_13064 <- eval (isBitSet v_13053 1);
      v_13066 <- getRegister sf;
      v_13073 <- getRegister pf;
      v_13077 <- eval (eq v_13050 (expression.bv_nat 8 1));
      v_13078 <- eval (uge v_13050 (expression.bv_nat 8 32));
      v_13083 <- getRegister cf;
      v_13088 <- eval (bit_or (bit_and v_13078 undef) (bit_and (notBool_ v_13078) (bit_or (bit_and v_13057 (isBitSet v_13053 0)) (bit_and v_13056 (eq v_13083 (expression.bv_nat 1 1))))));
      v_13093 <- eval (bit_and v_13057 undef);
      v_13094 <- getRegister of;
      v_13100 <- getRegister af;
      setRegister af (bit_or v_13093 (bit_and v_13056 (eq v_13100 (expression.bv_nat 1 1))));
      setRegister cf v_13088;
      setRegister of (bit_or (bit_and v_13077 (notBool_ (eq v_13088 v_13064))) (bit_and (notBool_ v_13077) (bit_or v_13093 (bit_and v_13056 (eq v_13094 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13057 (parityFlag (extract v_13053 25 33))) (bit_and v_13056 (eq v_13073 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13057 v_13064) (bit_and v_13056 (eq v_13066 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13057 (eq v_13054 (expression.bv_nat 32 0))) (bit_and v_13056 (eq v_13060 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2978 : imm int) (v_2979 : Mem) => do
      v_13110 <- evaluateAddress v_2979;
      v_13111 <- load v_13110 4;
      v_13114 <- eval (bv_and (handleImmediateWithSignExtend v_2978 8 8) (expression.bv_nat 8 31));
      v_13117 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13111) (concat (expression.bv_nat 25 0) v_13114)) 0 33);
      v_13118 <- eval (extract v_13117 1 33);
      store v_13110 v_13118 4;
      v_13120 <- eval (eq v_13114 (expression.bv_nat 8 0));
      v_13121 <- eval (notBool_ v_13120);
      v_13124 <- getRegister zf;
      v_13128 <- eval (isBitSet v_13117 1);
      v_13130 <- getRegister sf;
      v_13137 <- getRegister pf;
      v_13141 <- eval (eq v_13114 (expression.bv_nat 8 1));
      v_13142 <- eval (uge v_13114 (expression.bv_nat 8 32));
      v_13147 <- getRegister cf;
      v_13152 <- eval (bit_or (bit_and v_13142 undef) (bit_and (notBool_ v_13142) (bit_or (bit_and v_13121 (isBitSet v_13117 0)) (bit_and v_13120 (eq v_13147 (expression.bv_nat 1 1))))));
      v_13157 <- eval (bit_and v_13121 undef);
      v_13158 <- getRegister of;
      v_13164 <- getRegister af;
      setRegister af (bit_or v_13157 (bit_and v_13120 (eq v_13164 (expression.bv_nat 1 1))));
      setRegister cf v_13152;
      setRegister of (bit_or (bit_and v_13141 (notBool_ (eq v_13152 v_13128))) (bit_and (notBool_ v_13141) (bit_or v_13157 (bit_and v_13120 (eq v_13158 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13121 (parityFlag (extract v_13117 25 33))) (bit_and v_13120 (eq v_13137 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13121 v_13128) (bit_and v_13120 (eq v_13130 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13121 (eq v_13118 (expression.bv_nat 32 0))) (bit_and v_13120 (eq v_13124 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2982 : Mem) => do
      v_14510 <- evaluateAddress v_2982;
      v_14511 <- load v_14510 4;
      v_14514 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_14511) (expression.bv_nat 33 1)) 0 33);
      v_14515 <- eval (extract v_14514 1 33);
      store v_14510 v_14515 4;
      v_14518 <- eval (isBitSet v_14514 1);
      v_14521 <- eval (isBitSet v_14514 0);
      setRegister af undef;
      setRegister cf v_14521;
      setRegister of (notBool_ (eq v_14521 v_14518));
      setRegister pf (parityFlag (extract v_14514 25 33));
      setRegister sf v_14518;
      setRegister zf (zeroFlag v_14515);
      pure ()
    pat_end
