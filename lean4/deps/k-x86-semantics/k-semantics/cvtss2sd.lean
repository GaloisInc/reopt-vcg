def cvtss2sd1 : instruction :=
  definst "cvtss2sd" $ do
    pattern fun (v_2653 : reg (bv 128)) (v_2654 : reg (bv 128)) => do
      v_4266 <- getRegister v_2654;
      v_4268 <- getRegister v_2653;
      setRegister (lhs.of_reg v_2654) (concat (extract v_4266 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_4268 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2648 : Mem) (v_2649 : reg (bv 128)) => do
      v_7959 <- getRegister v_2649;
      v_7961 <- evaluateAddress v_2648;
      v_7962 <- load v_7961 4;
      setRegister (lhs.of_reg v_2649) (concat (extract v_7959 0 64) (Float2MInt (roundFloat (MInt2Float v_7962 24 8) 53 11) 64));
      pure ()
    pat_end
