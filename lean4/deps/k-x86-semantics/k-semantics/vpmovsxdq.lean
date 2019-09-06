def vpmovsxdq1 : instruction :=
  definst "vpmovsxdq" $ do
    pattern fun (v_2737 : reg (bv 128)) (v_2738 : reg (bv 128)) => do
      v_5651 <- getRegister v_2737;
      setRegister (lhs.of_reg v_2738) (concat (sext (extract v_5651 64 96) 64) (sext (extract v_5651 96 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2747 : reg (bv 128)) (v_2746 : reg (bv 256)) => do
      v_5662 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2746) (concat (sext (extract v_5662 0 32) 64) (concat (sext (extract v_5662 32 64) 64) (concat (sext (extract v_5662 64 96) 64) (sext (extract v_5662 96 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 128)) => do
      v_12064 <- evaluateAddress v_2732;
      v_12065 <- load v_12064 8;
      setRegister (lhs.of_reg v_2733) (concat (sext (extract v_12065 0 32) 64) (sext (extract v_12065 32 64) 64));
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) (v_2742 : reg (bv 256)) => do
      v_12072 <- evaluateAddress v_2741;
      v_12073 <- load v_12072 16;
      setRegister (lhs.of_reg v_2742) (concat (sext (extract v_12073 0 32) 64) (concat (sext (extract v_12073 32 64) 64) (concat (sext (extract v_12073 64 96) 64) (sext (extract v_12073 96 128) 64))));
      pure ()
    pat_end
