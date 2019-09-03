def movbe1 : instruction :=
  definst "movbe" $ do
    pattern fun (v_2393 : reg (bv 16)) (v_2394 : Mem) => do
      v_8801 <- evaluateAddress v_2394;
      v_8802 <- getRegister v_2393;
      store v_8801 (concat (extract v_8802 8 16) (extract v_8802 0 8)) 2;
      pure ()
    pat_end;
    pattern fun (v_2402 : Mem) (v_2401 : reg (bv 16)) => do
      v_10953 <- evaluateAddress v_2402;
      v_10954 <- load v_10953 2;
      setRegister (lhs.of_reg v_2401) (concat (extract v_10954 8 16) (extract v_10954 0 8));
      pure ()
    pat_end
