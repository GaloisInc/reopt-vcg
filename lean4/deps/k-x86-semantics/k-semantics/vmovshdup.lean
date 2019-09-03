def vmovshdup1 : instruction :=
  definst "vmovshdup" $ do
    pattern fun (v_2967 : reg (bv 128)) (v_2968 : reg (bv 128)) => do
      v_4985 <- getRegister v_2967;
      setRegister (lhs.of_reg v_2968) (concat (concat (extract v_4985 0 32) (extract v_4985 0 32)) (concat (extract v_4985 64 96) (extract v_4985 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2976 : reg (bv 256)) (v_2977 : reg (bv 256)) => do
      v_4996 <- getRegister v_2976;
      setRegister (lhs.of_reg v_2977) (concat (concat (concat (extract v_4996 0 32) (extract v_4996 0 32)) (concat (extract v_4996 64 96) (extract v_4996 64 96))) (concat (concat (extract v_4996 128 160) (extract v_4996 128 160)) (concat (extract v_4996 192 224) (extract v_4996 192 224))));
      pure ()
    pat_end;
    pattern fun (v_2962 : Mem) (v_2963 : reg (bv 128)) => do
      v_10355 <- evaluateAddress v_2962;
      v_10356 <- load v_10355 16;
      setRegister (lhs.of_reg v_2963) (concat (concat (extract v_10356 0 32) (extract v_10356 0 32)) (concat (extract v_10356 64 96) (extract v_10356 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2971 : Mem) (v_2972 : reg (bv 256)) => do
      v_10363 <- evaluateAddress v_2971;
      v_10364 <- load v_10363 32;
      setRegister (lhs.of_reg v_2972) (concat (concat (concat (extract v_10364 0 32) (extract v_10364 0 32)) (concat (extract v_10364 64 96) (extract v_10364 64 96))) (concat (concat (extract v_10364 128 160) (extract v_10364 128 160)) (concat (extract v_10364 192 224) (extract v_10364 192 224))));
      pure ()
    pat_end
