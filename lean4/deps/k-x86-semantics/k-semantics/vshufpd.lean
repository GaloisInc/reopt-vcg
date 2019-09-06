def vshufpd1 : instruction :=
  definst "vshufpd" $ do
    pattern fun (v_2997 : imm int) (v_2999 : reg (bv 128)) (v_3000 : reg (bv 128)) (v_3001 : reg (bv 128)) => do
      v_6878 <- eval (handleImmediateWithSignExtend v_2997 8 8);
      v_6880 <- getRegister v_2999;
      v_6885 <- getRegister v_3000;
      setRegister (lhs.of_reg v_3001) (concat (mux (isBitSet v_6878 6) (extract v_6880 0 64) (extract v_6880 64 128)) (mux (isBitSet v_6878 7) (extract v_6885 0 64) (extract v_6885 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3010 : imm int) (v_3012 : reg (bv 256)) (v_3013 : reg (bv 256)) (v_3014 : reg (bv 256)) => do
      v_6897 <- eval (handleImmediateWithSignExtend v_3010 8 8);
      v_6899 <- getRegister v_3012;
      v_6904 <- getRegister v_3013;
      setRegister (lhs.of_reg v_3014) (concat (mux (isBitSet v_6897 4) (extract v_6899 0 64) (extract v_6899 64 128)) (concat (mux (isBitSet v_6897 5) (extract v_6904 0 64) (extract v_6904 64 128)) (concat (mux (isBitSet v_6897 6) (extract v_6899 128 192) (extract v_6899 192 256)) (mux (isBitSet v_6897 7) (extract v_6904 128 192) (extract v_6904 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2991 : imm int) (v_2992 : Mem) (v_2993 : reg (bv 128)) (v_2994 : reg (bv 128)) => do
      v_12845 <- eval (handleImmediateWithSignExtend v_2991 8 8);
      v_12847 <- evaluateAddress v_2992;
      v_12848 <- load v_12847 16;
      v_12853 <- getRegister v_2993;
      setRegister (lhs.of_reg v_2994) (concat (mux (isBitSet v_12845 6) (extract v_12848 0 64) (extract v_12848 64 128)) (mux (isBitSet v_12845 7) (extract v_12853 0 64) (extract v_12853 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3004 : imm int) (v_3005 : Mem) (v_3006 : reg (bv 256)) (v_3007 : reg (bv 256)) => do
      v_12859 <- eval (handleImmediateWithSignExtend v_3004 8 8);
      v_12861 <- evaluateAddress v_3005;
      v_12862 <- load v_12861 32;
      v_12867 <- getRegister v_3006;
      setRegister (lhs.of_reg v_3007) (concat (mux (isBitSet v_12859 4) (extract v_12862 0 64) (extract v_12862 64 128)) (concat (mux (isBitSet v_12859 5) (extract v_12867 0 64) (extract v_12867 64 128)) (concat (mux (isBitSet v_12859 6) (extract v_12862 128 192) (extract v_12862 192 256)) (mux (isBitSet v_12859 7) (extract v_12867 128 192) (extract v_12867 192 256)))));
      pure ()
    pat_end
