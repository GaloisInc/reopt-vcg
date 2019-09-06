def punpckldq1 : instruction :=
  definst "punpckldq" $ do
    pattern fun (v_3298 : reg (bv 128)) (v_3299 : reg (bv 128)) => do
      v_8808 <- getRegister v_3298;
      v_8810 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3299) (concat (concat (extract v_8808 64 96) (extract v_8810 64 96)) (concat (extract v_8808 96 128) (extract v_8810 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3294 : Mem) (v_3295 : reg (bv 128)) => do
      v_15196 <- evaluateAddress v_3294;
      v_15197 <- load v_15196 16;
      v_15199 <- getRegister v_3295;
      setRegister (lhs.of_reg v_3295) (concat (concat (extract v_15197 64 96) (extract v_15199 64 96)) (concat (extract v_15197 96 128) (extract v_15199 96 128)));
      pure ()
    pat_end
