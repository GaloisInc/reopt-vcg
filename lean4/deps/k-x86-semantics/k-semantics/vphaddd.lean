def vphaddd1 : instruction :=
  definst "vphaddd" $ do
    pattern fun (v_3150 : reg (bv 128)) (v_3151 : reg (bv 128)) (v_3152 : reg (bv 128)) => do
      v_8959 <- getRegister v_3150;
      v_8967 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3152) (concat (concat (concat (add (extract v_8959 0 32) (extract v_8959 32 64)) (add (extract v_8959 64 96) (extract v_8959 96 128))) (add (extract v_8967 0 32) (extract v_8967 32 64))) (add (extract v_8967 64 96) (extract v_8967 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3161 : reg (bv 256)) (v_3162 : reg (bv 256)) (v_3163 : reg (bv 256)) => do
      v_8982 <- getRegister v_3161;
      v_8990 <- getRegister v_3162;
      setRegister (lhs.of_reg v_3163) (concat (concat (concat (concat (add (extract v_8982 0 32) (extract v_8982 32 64)) (add (extract v_8982 64 96) (extract v_8982 96 128))) (add (extract v_8990 0 32) (extract v_8990 32 64))) (add (extract v_8990 64 96) (extract v_8990 96 128))) (concat (concat (concat (add (extract v_8982 128 160) (extract v_8982 160 192)) (add (extract v_8982 192 224) (extract v_8982 224 256))) (add (extract v_8990 128 160) (extract v_8990 160 192))) (add (extract v_8990 192 224) (extract v_8990 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3145 : reg (bv 128)) (v_3146 : reg (bv 128)) => do
      v_17987 <- evaluateAddress v_3144;
      v_17988 <- load v_17987 16;
      v_17996 <- getRegister v_3145;
      setRegister (lhs.of_reg v_3146) (concat (concat (concat (add (extract v_17988 0 32) (extract v_17988 32 64)) (add (extract v_17988 64 96) (extract v_17988 96 128))) (add (extract v_17996 0 32) (extract v_17996 32 64))) (add (extract v_17996 64 96) (extract v_17996 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3155 : Mem) (v_3156 : reg (bv 256)) (v_3157 : reg (bv 256)) => do
      v_18006 <- evaluateAddress v_3155;
      v_18007 <- load v_18006 32;
      v_18015 <- getRegister v_3156;
      setRegister (lhs.of_reg v_3157) (concat (concat (concat (concat (add (extract v_18007 0 32) (extract v_18007 32 64)) (add (extract v_18007 64 96) (extract v_18007 96 128))) (add (extract v_18015 0 32) (extract v_18015 32 64))) (add (extract v_18015 64 96) (extract v_18015 96 128))) (concat (concat (concat (add (extract v_18007 128 160) (extract v_18007 160 192)) (add (extract v_18007 192 224) (extract v_18007 224 256))) (add (extract v_18015 128 160) (extract v_18015 160 192))) (add (extract v_18015 192 224) (extract v_18015 224 256))));
      pure ()
    pat_end
