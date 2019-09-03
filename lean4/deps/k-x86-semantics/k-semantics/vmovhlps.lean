def vmovhlps1 : instruction :=
  definst "vmovhlps" $ do
    pattern fun (v_2818 : reg (bv 128)) (v_2819 : reg (bv 128)) (v_2820 : reg (bv 128)) => do
      v_5134 <- getRegister v_2819;
      v_5136 <- getRegister v_2818;
      setRegister (lhs.of_reg v_2820) (concat (extract v_5134 0 64) (extract v_5136 0 64));
      pure ()
    pat_end
