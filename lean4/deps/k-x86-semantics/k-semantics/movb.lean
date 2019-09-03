def movb1 : instruction :=
  definst "movb" $ do
    pattern fun (v_3157 : imm int) (v_3158 : reg (bv 8)) => do
      setRegister (lhs.of_reg v_3158) (handleImmediateWithSignExtend v_3157 8 8);
      pure ()
    pat_end;
    pattern fun (v_3166 : reg (bv 8)) (v_3167 : reg (bv 8)) => do
      v_5915 <- getRegister v_3166;
      setRegister (lhs.of_reg v_3167) v_5915;
      pure ()
    pat_end;
    pattern fun (v_3146 : imm int) (v_3145 : Mem) => do
      v_7669 <- evaluateAddress v_3145;
      store v_7669 (handleImmediateWithSignExtend v_3146 8 8) 1;
      pure ()
    pat_end;
    pattern fun (v_3150 : reg (bv 8)) (v_3149 : Mem) => do
      v_7672 <- evaluateAddress v_3149;
      v_7673 <- getRegister v_3150;
      store v_7672 v_7673 1;
      pure ()
    pat_end;
    pattern fun (v_3162 : Mem) (v_3163 : reg (bv 8)) => do
      v_9312 <- evaluateAddress v_3162;
      v_9313 <- load v_9312 1;
      setRegister (lhs.of_reg v_3163) v_9313;
      pure ()
    pat_end
