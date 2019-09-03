def psubq1 : instruction :=
  definst "psubq" $ do
    pattern fun (v_3113 : reg (bv 128)) (v_3114 : reg (bv 128)) => do
      v_8103 <- getRegister v_3114;
      v_8105 <- getRegister v_3113;
      setRegister (lhs.of_reg v_3114) (concat (sub (extract v_8103 0 64) (extract v_8105 0 64)) (sub (extract v_8103 64 128) (extract v_8105 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3109 : Mem) (v_3110 : reg (bv 128)) => do
      v_14715 <- getRegister v_3110;
      v_14717 <- evaluateAddress v_3109;
      v_14718 <- load v_14717 16;
      setRegister (lhs.of_reg v_3110) (concat (sub (extract v_14715 0 64) (extract v_14718 0 64)) (sub (extract v_14715 64 128) (extract v_14718 64 128)));
      pure ()
    pat_end
