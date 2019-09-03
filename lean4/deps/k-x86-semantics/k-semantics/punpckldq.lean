def punpckldq1 : instruction :=
  definst "punpckldq" $ do
    pattern fun (v_3221 : reg (bv 128)) (v_3222 : reg (bv 128)) => do
      v_8847 <- getRegister v_3221;
      v_8849 <- getRegister v_3222;
      setRegister (lhs.of_reg v_3222) (concat (concat (extract v_8847 64 96) (extract v_8849 64 96)) (concat (extract v_8847 96 128) (extract v_8849 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3217 : Mem) (v_3218 : reg (bv 128)) => do
      v_15423 <- evaluateAddress v_3217;
      v_15424 <- load v_15423 16;
      v_15426 <- getRegister v_3218;
      setRegister (lhs.of_reg v_3218) (concat (concat (extract v_15424 64 96) (extract v_15426 64 96)) (concat (extract v_15424 96 128) (extract v_15426 96 128)));
      pure ()
    pat_end
