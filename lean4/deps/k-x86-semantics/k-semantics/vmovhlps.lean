def vmovhlps1 : instruction :=
  definst "vmovhlps" $ do
    pattern fun (v_2806 : reg (bv 128)) (v_2807 : reg (bv 128)) (v_2808 : reg (bv 128)) => do
      v_4761 <- getRegister v_2807;
      v_4763 <- getRegister v_2806;
      setRegister (lhs.of_reg v_2808) (concat (extract v_4761 0 64) (extract v_4763 0 64));
      pure ()
    pat_end
