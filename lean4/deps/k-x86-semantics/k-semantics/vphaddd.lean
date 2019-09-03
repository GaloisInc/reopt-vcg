def vphaddd1 : instruction :=
  definst "vphaddd" $ do
    pattern fun (v_3160 : reg (bv 128)) (v_3161 : reg (bv 128)) (v_3162 : reg (bv 128)) => do
      v_8808 <- getRegister v_3160;
      v_8816 <- getRegister v_3161;
      setRegister (lhs.of_reg v_3162) (concat (concat (concat (add (extract v_8808 0 32) (extract v_8808 32 64)) (add (extract v_8808 64 96) (extract v_8808 96 128))) (add (extract v_8816 0 32) (extract v_8816 32 64))) (add (extract v_8816 64 96) (extract v_8816 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3174 : reg (bv 256)) (v_3175 : reg (bv 256)) (v_3176 : reg (bv 256)) => do
      v_8831 <- getRegister v_3174;
      v_8839 <- getRegister v_3175;
      setRegister (lhs.of_reg v_3176) (concat (concat (concat (concat (add (extract v_8831 0 32) (extract v_8831 32 64)) (add (extract v_8831 64 96) (extract v_8831 96 128))) (add (extract v_8839 0 32) (extract v_8839 32 64))) (add (extract v_8839 64 96) (extract v_8839 96 128))) (concat (concat (concat (add (extract v_8831 128 160) (extract v_8831 160 192)) (add (extract v_8831 192 224) (extract v_8831 224 256))) (add (extract v_8839 128 160) (extract v_8839 160 192))) (add (extract v_8839 192 224) (extract v_8839 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3155 : reg (bv 128)) (v_3156 : reg (bv 128)) => do
      v_17470 <- evaluateAddress v_3159;
      v_17471 <- load v_17470 16;
      v_17479 <- getRegister v_3155;
      setRegister (lhs.of_reg v_3156) (concat (concat (concat (add (extract v_17471 0 32) (extract v_17471 32 64)) (add (extract v_17471 64 96) (extract v_17471 96 128))) (add (extract v_17479 0 32) (extract v_17479 32 64))) (add (extract v_17479 64 96) (extract v_17479 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3169 : reg (bv 256)) (v_3170 : reg (bv 256)) => do
      v_17489 <- evaluateAddress v_3168;
      v_17490 <- load v_17489 32;
      v_17498 <- getRegister v_3169;
      setRegister (lhs.of_reg v_3170) (concat (concat (concat (concat (add (extract v_17490 0 32) (extract v_17490 32 64)) (add (extract v_17490 64 96) (extract v_17490 96 128))) (add (extract v_17498 0 32) (extract v_17498 32 64))) (add (extract v_17498 64 96) (extract v_17498 96 128))) (concat (concat (concat (add (extract v_17490 128 160) (extract v_17490 160 192)) (add (extract v_17490 192 224) (extract v_17490 224 256))) (add (extract v_17498 128 160) (extract v_17498 160 192))) (add (extract v_17498 192 224) (extract v_17498 224 256))));
      pure ()
    pat_end
