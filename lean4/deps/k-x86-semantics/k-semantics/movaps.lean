def movaps1 : instruction :=
  definst "movaps" $ do
    pattern fun (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_5727 <- getRegister v_3205;
      setRegister (lhs.of_reg v_3206) v_5727;
      pure ()
    pat_end;
    pattern fun (v_3197 : reg (bv 128)) (v_3196 : Mem) => do
      v_7497 <- evaluateAddress v_3196;
      v_7498 <- getRegister v_3197;
      store v_7497 v_7498 16;
      pure ()
    pat_end;
    pattern fun (v_3200 : Mem) (v_3201 : reg (bv 128)) => do
      v_8949 <- evaluateAddress v_3200;
      v_8950 <- load v_8949 16;
      setRegister (lhs.of_reg v_3201) v_8950;
      pure ()
    pat_end
