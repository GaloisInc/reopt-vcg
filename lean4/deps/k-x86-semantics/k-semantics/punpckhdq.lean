def punpckhdq1 : instruction :=
  definst "punpckhdq" $ do
    pattern fun (v_3234 : reg (bv 128)) (v_3235 : reg (bv 128)) => do
      v_8697 <- getRegister v_3234;
      v_8699 <- getRegister v_3235;
      setRegister (lhs.of_reg v_3235) (concat (concat (extract v_8697 0 32) (extract v_8699 0 32)) (concat (extract v_8697 32 64) (extract v_8699 32 64)));
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3230 : reg (bv 128)) => do
      v_15148 <- evaluateAddress v_3231;
      v_15149 <- load v_15148 16;
      v_15151 <- getRegister v_3230;
      setRegister (lhs.of_reg v_3230) (concat (concat (extract v_15149 0 32) (extract v_15151 0 32)) (concat (extract v_15149 32 64) (extract v_15151 32 64)));
      pure ()
    pat_end
