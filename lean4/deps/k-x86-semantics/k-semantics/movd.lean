def movd1 : instruction :=
  definst "movd" $ do
    pattern fun (v_2464 : reg (bv 128)) (v_2465 : reg (bv 32)) => do
      v_3896 <- getRegister v_2464;
      setRegister (lhs.of_reg v_2465) (extract v_3896 96 128);
      pure ()
    pat_end;
    pattern fun (v_2474 : reg (bv 32)) (v_2473 : reg (bv 128)) => do
      v_3903 <- getRegister v_2474;
      setRegister (lhs.of_reg v_2473) (concat (expression.bv_nat 96 0) v_3903);
      pure ()
    pat_end;
    pattern fun (v_2460 : reg (bv 128)) (v_2459 : Mem) => do
      v_8417 <- evaluateAddress v_2459;
      v_8418 <- getRegister v_2460;
      store v_8417 (extract v_8418 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2468 : Mem) (v_2469 : reg (bv 128)) => do
      v_8678 <- evaluateAddress v_2468;
      v_8679 <- load v_8678 4;
      setRegister (lhs.of_reg v_2469) (concat (expression.bv_nat 96 0) v_8679);
      pure ()
    pat_end
