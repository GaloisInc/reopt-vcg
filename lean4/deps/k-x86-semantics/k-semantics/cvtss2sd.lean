def cvtss2sd1 : instruction :=
  definst "cvtss2sd" $ do
    pattern fun (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_4256 <- getRegister v_2589;
      v_4258 <- getRegister v_2588;
      setRegister (lhs.of_reg v_2589) (concat (extract v_4256 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_4258 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2584 : Mem) (v_2585 : reg (bv 128)) => do
      v_8181 <- getRegister v_2585;
      v_8183 <- evaluateAddress v_2584;
      v_8184 <- load v_8183 4;
      setRegister (lhs.of_reg v_2585) (concat (extract v_8181 0 64) (Float2MInt (roundFloat (MInt2Float v_8184 24 8) 53 11) 64));
      pure ()
    pat_end
