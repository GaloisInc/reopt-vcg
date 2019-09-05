def movmskpd1 : instruction :=
  definst "movmskpd" $ do
    pattern fun (v_2577 : reg (bv 128)) (v_2578 : reg (bv 32)) => do
      v_3994 <- getRegister v_2577;
      setRegister (lhs.of_reg v_2578) (concat (expression.bv_nat 30 0) (concat (extract v_3994 0 1) (extract v_3994 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2583 : reg (bv 128)) (v_2581 : reg (bv 64)) => do
      v_4000 <- getRegister v_2583;
      setRegister (lhs.of_reg v_2581) (concat (expression.bv_nat 62 0) (concat (extract v_4000 0 1) (extract v_4000 64 65)));
      pure ()
    pat_end
