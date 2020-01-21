def movhlps : instruction :=
  definst "movhlps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (extract v_3 0 64));
      pure ()
    pat_end
