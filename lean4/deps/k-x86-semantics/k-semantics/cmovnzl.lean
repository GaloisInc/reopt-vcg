def cmovnzl1 : instruction :=
  definst "cmovnzl" $ do
    pattern fun (v_3184 : reg (bv 32)) (v_3185 : reg (bv 32)) => do
      v_4946 <- getRegister zf;
      v_4948 <- getRegister v_3184;
      v_4949 <- getRegister v_3185;
      setRegister (lhs.of_reg v_3185) (mux (notBool_ v_4946) v_4948 v_4949);
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3180 : reg (bv 32)) => do
      v_8213 <- getRegister zf;
      v_8215 <- evaluateAddress v_3177;
      v_8216 <- load v_8215 4;
      v_8217 <- getRegister v_3180;
      setRegister (lhs.of_reg v_3180) (mux (notBool_ v_8213) v_8216 v_8217);
      pure ()
    pat_end
