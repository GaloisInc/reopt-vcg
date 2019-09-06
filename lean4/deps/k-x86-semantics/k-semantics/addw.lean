def addw1 : instruction :=
  definst "addw" $ do
    pattern fun (v_2775 : imm int) (v_2776 : reg (bv 16)) => do
      v_4913 <- eval (handleImmediateWithSignExtend v_2775 16 16);
      v_4915 <- getRegister v_2776;
      v_4917 <- eval (add (concat (expression.bv_nat 1 0) v_4913) (concat (expression.bv_nat 1 0) v_4915));
      v_4918 <- eval (extract v_4917 1 17);
      setRegister (lhs.of_reg v_2776) v_4918;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4913 v_4915) 11) (isBitSet v_4917 12)));
      setRegister cf (isBitSet v_4917 0);
      setRegister of (overflowFlag v_4913 v_4915 v_4918);
      setRegister pf (parityFlag (extract v_4917 9 17));
      setRegister sf (isBitSet v_4917 1);
      setRegister zf (zeroFlag v_4918);
      pure ()
    pat_end;
    pattern fun (v_2784 : reg (bv 16)) (v_2785 : reg (bv 16)) => do
      v_4941 <- getRegister v_2784;
      v_4943 <- getRegister v_2785;
      v_4945 <- eval (add (concat (expression.bv_nat 1 0) v_4941) (concat (expression.bv_nat 1 0) v_4943));
      v_4946 <- eval (extract v_4945 1 17);
      setRegister (lhs.of_reg v_2785) v_4946;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4941 v_4943) 11) (isBitSet v_4945 12)));
      setRegister cf (isBitSet v_4945 0);
      setRegister of (overflowFlag v_4941 v_4943 v_4946);
      setRegister pf (parityFlag (extract v_4945 9 17));
      setRegister sf (isBitSet v_4945 1);
      setRegister zf (zeroFlag v_4946);
      pure ()
    pat_end;
    pattern fun (v_2780 : Mem) (v_2781 : reg (bv 16)) => do
      v_8897 <- evaluateAddress v_2780;
      v_8898 <- load v_8897 2;
      v_8900 <- getRegister v_2781;
      v_8902 <- eval (add (concat (expression.bv_nat 1 0) v_8898) (concat (expression.bv_nat 1 0) v_8900));
      v_8903 <- eval (extract v_8902 1 17);
      setRegister (lhs.of_reg v_2781) v_8903;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8898 v_8900) 11) (isBitSet v_8902 12)));
      setRegister cf (isBitSet v_8902 0);
      setRegister of (overflowFlag v_8898 v_8900 v_8903);
      setRegister pf (parityFlag (extract v_8902 9 17));
      setRegister sf (isBitSet v_8902 1);
      setRegister zf (zeroFlag v_8903);
      pure ()
    pat_end;
    pattern fun (v_2768 : imm int) (v_2767 : Mem) => do
      v_10234 <- evaluateAddress v_2767;
      v_10235 <- eval (handleImmediateWithSignExtend v_2768 16 16);
      v_10237 <- load v_10234 2;
      v_10239 <- eval (add (concat (expression.bv_nat 1 0) v_10235) (concat (expression.bv_nat 1 0) v_10237));
      v_10240 <- eval (extract v_10239 1 17);
      store v_10234 v_10240 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10235 v_10237) 11) (isBitSet v_10239 12)));
      setRegister cf (isBitSet v_10239 0);
      setRegister of (overflowFlag v_10235 v_10237 v_10240);
      setRegister pf (parityFlag (extract v_10239 9 17));
      setRegister sf (isBitSet v_10239 1);
      setRegister zf (zeroFlag v_10240);
      pure ()
    pat_end;
    pattern fun (v_2772 : reg (bv 16)) (v_2771 : Mem) => do
      v_10259 <- evaluateAddress v_2771;
      v_10260 <- getRegister v_2772;
      v_10262 <- load v_10259 2;
      v_10264 <- eval (add (concat (expression.bv_nat 1 0) v_10260) (concat (expression.bv_nat 1 0) v_10262));
      v_10265 <- eval (extract v_10264 1 17);
      store v_10259 v_10265 2;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10260 v_10262) 11) (isBitSet v_10264 12)));
      setRegister cf (isBitSet v_10264 0);
      setRegister of (overflowFlag v_10260 v_10262 v_10265);
      setRegister pf (parityFlag (extract v_10264 9 17));
      setRegister sf (isBitSet v_10264 1);
      setRegister zf (zeroFlag v_10265);
      pure ()
    pat_end
