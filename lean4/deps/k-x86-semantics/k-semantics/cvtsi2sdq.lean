def cvtsi2sdq1 : instruction :=
  definst "cvtsi2sdq" $ do
    pattern fun (v_2625 : reg (bv 64)) (v_2627 : reg (bv 128)) => do
      v_4230 <- getRegister v_2627;
      v_4232 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2627) (concat (extract v_4230 0 64) (Float2MInt (Int2Float (svalueMInt v_4232) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2621 : Mem) (v_2622 : reg (bv 128)) => do
      v_7932 <- getRegister v_2622;
      v_7934 <- evaluateAddress v_2621;
      v_7935 <- load v_7934 8;
      setRegister (lhs.of_reg v_2622) (concat (extract v_7932 0 64) (Float2MInt (Int2Float (svalueMInt v_7935) 53 11) 64));
      pure ()
    pat_end
