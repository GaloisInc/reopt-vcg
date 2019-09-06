def vpmovsxwq1 : instruction :=
  definst "vpmovsxwq" $ do
    pattern fun (v_2773 : reg (bv 128)) (v_2774 : reg (bv 128)) => do
      v_5725 <- getRegister v_2773;
      setRegister (lhs.of_reg v_2774) (concat (sext (extract v_5725 96 112) 64) (sext (extract v_5725 112 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2783 : reg (bv 128)) (v_2782 : reg (bv 256)) => do
      v_5736 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2782) (concat (sext (extract v_5736 64 80) 64) (concat (sext (extract v_5736 80 96) 64) (concat (sext (extract v_5736 96 112) 64) (sext (extract v_5736 112 128) 64))));
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) (v_2769 : reg (bv 128)) => do
      v_12126 <- evaluateAddress v_2768;
      v_12127 <- load v_12126 4;
      setRegister (lhs.of_reg v_2769) (concat (sext (extract v_12127 0 16) 64) (sext (extract v_12127 16 32) 64));
      pure ()
    pat_end;
    pattern fun (v_2777 : Mem) (v_2778 : reg (bv 256)) => do
      v_12134 <- evaluateAddress v_2777;
      v_12135 <- load v_12134 8;
      setRegister (lhs.of_reg v_2778) (concat (sext (extract v_12135 0 16) 64) (concat (sext (extract v_12135 16 32) 64) (concat (sext (extract v_12135 32 48) 64) (sext (extract v_12135 48 64) 64))));
      pure ()
    pat_end
