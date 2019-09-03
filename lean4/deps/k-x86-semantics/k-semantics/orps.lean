def orps1 : instruction :=
  definst "orps" $ do
    pattern fun (v_2999 : reg (bv 128)) (v_3000 : reg (bv 128)) => do
      v_4907 <- getRegister v_3000;
      v_4908 <- getRegister v_2999;
      setRegister (lhs.of_reg v_3000) (bv_or v_4907 v_4908);
      pure ()
    pat_end;
    pattern fun (v_2995 : Mem) (v_2996 : reg (bv 128)) => do
      v_9228 <- getRegister v_2996;
      v_9229 <- evaluateAddress v_2995;
      v_9230 <- load v_9229 16;
      setRegister (lhs.of_reg v_2996) (bv_or v_9228 v_9230);
      pure ()
    pat_end
