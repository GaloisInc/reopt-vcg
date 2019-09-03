def paddq1 : instruction :=
  definst "paddq" $ do
    pattern fun (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) => do
      v_5766 <- getRegister v_3130;
      v_5768 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3130) (concat (add (extract v_5766 0 64) (extract v_5768 0 64)) (add (extract v_5766 64 128) (extract v_5768 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3124 : Mem) (v_3125 : reg (bv 128)) => do
      v_9856 <- getRegister v_3125;
      v_9858 <- evaluateAddress v_3124;
      v_9859 <- load v_9858 16;
      setRegister (lhs.of_reg v_3125) (concat (add (extract v_9856 0 64) (extract v_9859 0 64)) (add (extract v_9856 64 128) (extract v_9859 64 128)));
      pure ()
    pat_end
