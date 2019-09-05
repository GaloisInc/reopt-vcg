def movhlps1 : instruction :=
  definst "movhlps" $ do
    pattern fun (v_2513 : reg (bv 128)) (v_2514 : reg (bv 128)) => do
      v_3934 <- getRegister v_2514;
      v_3936 <- getRegister v_2513;
      setRegister (lhs.of_reg v_2514) (concat (extract v_3934 0 64) (extract v_3936 0 64));
      pure ()
    pat_end
