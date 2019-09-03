def movlhps1 : instruction :=
  definst "movlhps" $ do
    pattern fun (v_2493 : reg (bv 128)) (v_2494 : reg (bv 128)) => do
      v_3908 <- getRegister v_2493;
      v_3910 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2494) (concat (extract v_3908 64 128) (extract v_3910 64 128));
      pure ()
    pat_end
