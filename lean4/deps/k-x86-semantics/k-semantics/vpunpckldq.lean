def vpunpckldq1 : instruction :=
  definst "vpunpckldq" $ do
    pattern fun (v_2781 : reg (bv 128)) (v_2782 : reg (bv 128)) (v_2783 : reg (bv 128)) => do
      v_6442 <- getRegister v_2781;
      v_6444 <- getRegister v_2782;
      setRegister (lhs.of_reg v_2783) (concat (concat (extract v_6442 64 96) (extract v_6444 64 96)) (concat (extract v_6442 96 128) (extract v_6444 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2792 : reg (bv 256)) (v_2793 : reg (bv 256)) (v_2794 : reg (bv 256)) => do
      v_6457 <- getRegister v_2792;
      v_6459 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2794) (concat (concat (extract v_6457 64 96) (extract v_6459 64 96)) (concat (concat (extract v_6457 96 128) (extract v_6459 96 128)) (concat (concat (extract v_6457 192 224) (extract v_6459 192 224)) (concat (extract v_6457 224 256) (extract v_6459 224 256)))));
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) (v_2776 : reg (bv 128)) (v_2777 : reg (bv 128)) => do
      v_12492 <- evaluateAddress v_2775;
      v_12493 <- load v_12492 16;
      v_12495 <- getRegister v_2776;
      setRegister (lhs.of_reg v_2777) (concat (concat (extract v_12493 64 96) (extract v_12495 64 96)) (concat (extract v_12493 96 128) (extract v_12495 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2787 : reg (bv 256)) (v_2788 : reg (bv 256)) => do
      v_12503 <- evaluateAddress v_2786;
      v_12504 <- load v_12503 32;
      v_12506 <- getRegister v_2787;
      setRegister (lhs.of_reg v_2788) (concat (concat (extract v_12504 64 96) (extract v_12506 64 96)) (concat (concat (extract v_12504 96 128) (extract v_12506 96 128)) (concat (concat (extract v_12504 192 224) (extract v_12506 192 224)) (concat (extract v_12504 224 256) (extract v_12506 224 256)))));
      pure ()
    pat_end
