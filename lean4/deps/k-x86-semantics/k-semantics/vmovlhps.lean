def vmovlhps1 : instruction :=
  definst "vmovlhps" $ do
    pattern fun (v_2830 : reg (bv 128)) (v_2831 : reg (bv 128)) (v_2832 : reg (bv 128)) => do
      v_4785 <- getRegister v_2830;
      v_4787 <- getRegister v_2831;
      setRegister (lhs.of_reg v_2832) (concat (extract v_4785 64 128) (extract v_4787 64 128));
      pure ()
    pat_end
