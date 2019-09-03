def punpckhdq1 : instruction :=
  definst "punpckhdq" $ do
    pattern fun (v_3185 : reg (bv 128)) (v_3186 : reg (bv 128)) => do
      v_8763 <- getRegister v_3185;
      v_8765 <- getRegister v_3186;
      setRegister (lhs.of_reg v_3186) (concat (concat (extract v_8763 0 32) (extract v_8765 0 32)) (concat (extract v_8763 32 64) (extract v_8765 32 64)));
      pure ()
    pat_end;
    pattern fun (v_3181 : Mem) (v_3182 : reg (bv 128)) => do
      v_15351 <- evaluateAddress v_3181;
      v_15352 <- load v_15351 16;
      v_15354 <- getRegister v_3182;
      setRegister (lhs.of_reg v_3182) (concat (concat (extract v_15352 0 32) (extract v_15354 0 32)) (concat (extract v_15352 32 64) (extract v_15354 32 64)));
      pure ()
    pat_end
