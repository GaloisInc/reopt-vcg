def movhlps1 : instruction :=
  definst "movhlps" $ do
    pattern fun (v_2450 : reg (bv 128)) (v_2451 : reg (bv 128)) => do
      v_3870 <- getRegister v_2451;
      v_3872 <- getRegister v_2450;
      setRegister (lhs.of_reg v_2451) (concat (extract v_3870 0 64) (extract v_3872 0 64));
      pure ()
    pat_end
