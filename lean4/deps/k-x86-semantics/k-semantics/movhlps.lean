def movhlps1 : instruction :=
  definst "movhlps" $ do
    pattern fun (v_2462 : reg (bv 128)) (v_2463 : reg (bv 128)) => do
      v_3883 <- getRegister v_2463;
      v_3885 <- getRegister v_2462;
      setRegister (lhs.of_reg v_2463) (concat (extract v_3883 0 64) (extract v_3885 0 64));
      pure ()
    pat_end
