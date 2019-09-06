def cvtsi2ssq1 : instruction :=
  definst "cvtsi2ssq" $ do
    pattern fun (v_2671 : reg (bv 64)) (v_2670 : reg (bv 128)) => do
      v_4275 <- getRegister v_2670;
      v_4277 <- getRegister v_2671;
      setRegister (lhs.of_reg v_2670) (concat (extract v_4275 0 96) (Float2MInt (Int2Float (svalueMInt v_4277) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2666 : Mem) (v_2667 : reg (bv 128)) => do
      v_7960 <- getRegister v_2667;
      v_7962 <- evaluateAddress v_2666;
      v_7963 <- load v_7962 8;
      setRegister (lhs.of_reg v_2667) (concat (extract v_7960 0 96) (Float2MInt (Int2Float (svalueMInt v_7963) 24 8) 32));
      pure ()
    pat_end
