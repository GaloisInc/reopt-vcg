def punpckldq1 : instruction :=
  definst "punpckldq" $ do
    pattern fun (v_3270 : reg (bv 128)) (v_3271 : reg (bv 128)) => do
      v_8781 <- getRegister v_3270;
      v_8783 <- getRegister v_3271;
      setRegister (lhs.of_reg v_3271) (concat (concat (extract v_8781 64 96) (extract v_8783 64 96)) (concat (extract v_8781 96 128) (extract v_8783 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3266 : reg (bv 128)) => do
      v_15220 <- evaluateAddress v_3267;
      v_15221 <- load v_15220 16;
      v_15223 <- getRegister v_3266;
      setRegister (lhs.of_reg v_3266) (concat (concat (extract v_15221 64 96) (extract v_15223 64 96)) (concat (extract v_15221 96 128) (extract v_15223 96 128)));
      pure ()
    pat_end
