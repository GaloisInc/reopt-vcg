def vmovlhps : instruction :=
  definst "vmovlhps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 64 128) (extract v_4 64 128));
      pure ()
    pat_end
