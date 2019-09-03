def punpckhqdq1 : instruction :=
  definst "punpckhqdq" $ do
    pattern fun (v_3194 : reg (bv 128)) (v_3195 : reg (bv 128)) => do
      v_8777 <- getRegister v_3194;
      v_8779 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3195) (concat (extract v_8777 0 64) (extract v_8779 0 64));
      pure ()
    pat_end;
    pattern fun (v_3190 : Mem) (v_3191 : reg (bv 128)) => do
      v_15362 <- evaluateAddress v_3190;
      v_15363 <- load v_15362 16;
      v_15365 <- getRegister v_3191;
      setRegister (lhs.of_reg v_3191) (concat (extract v_15363 0 64) (extract v_15365 0 64));
      pure ()
    pat_end
