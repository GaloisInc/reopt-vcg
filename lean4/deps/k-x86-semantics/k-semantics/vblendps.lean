def vblendps1 : instruction :=
  definst "vblendps" $ do
    pattern fun (v_2883 : imm int) (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) (v_2889 : reg (bv 128)) => do
      v_5277 <- eval (handleImmediateWithSignExtend v_2883 8 8);
      v_5279 <- getRegister v_2888;
      v_5281 <- getRegister v_2887;
      setRegister (lhs.of_reg v_2889) (concat (mux (isBitClear v_5277 4) (extract v_5279 0 32) (extract v_5281 0 32)) (concat (mux (isBitClear v_5277 5) (extract v_5279 32 64) (extract v_5281 32 64)) (concat (mux (isBitClear v_5277 6) (extract v_5279 64 96) (extract v_5281 64 96)) (mux (isBitClear v_5277 7) (extract v_5279 96 128) (extract v_5281 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2896 : imm int) (v_2897 : reg (bv 256)) (v_2898 : reg (bv 256)) (v_2899 : reg (bv 256)) => do
      v_5306 <- eval (handleImmediateWithSignExtend v_2896 8 8);
      v_5308 <- getRegister v_2898;
      v_5310 <- getRegister v_2897;
      setRegister (lhs.of_reg v_2899) (concat (mux (isBitClear v_5306 0) (extract v_5308 0 32) (extract v_5310 0 32)) (concat (mux (isBitClear v_5306 1) (extract v_5308 32 64) (extract v_5310 32 64)) (concat (mux (isBitClear v_5306 2) (extract v_5308 64 96) (extract v_5310 64 96)) (concat (mux (isBitClear v_5306 3) (extract v_5308 96 128) (extract v_5310 96 128)) (concat (mux (isBitClear v_5306 4) (extract v_5308 128 160) (extract v_5310 128 160)) (concat (mux (isBitClear v_5306 5) (extract v_5308 160 192) (extract v_5310 160 192)) (concat (mux (isBitClear v_5306 6) (extract v_5308 192 224) (extract v_5310 192 224)) (mux (isBitClear v_5306 7) (extract v_5308 224 256) (extract v_5310 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2877 : imm int) (v_2878 : Mem) (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) => do
      v_9501 <- eval (handleImmediateWithSignExtend v_2877 8 8);
      v_9503 <- getRegister v_2881;
      v_9505 <- evaluateAddress v_2878;
      v_9506 <- load v_9505 16;
      setRegister (lhs.of_reg v_2882) (concat (mux (isBitClear v_9501 4) (extract v_9503 0 32) (extract v_9506 0 32)) (concat (mux (isBitClear v_9501 5) (extract v_9503 32 64) (extract v_9506 32 64)) (concat (mux (isBitClear v_9501 6) (extract v_9503 64 96) (extract v_9506 64 96)) (mux (isBitClear v_9501 7) (extract v_9503 96 128) (extract v_9506 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2890 : imm int) (v_2891 : Mem) (v_2892 : reg (bv 256)) (v_2893 : reg (bv 256)) => do
      v_9525 <- eval (handleImmediateWithSignExtend v_2890 8 8);
      v_9527 <- getRegister v_2892;
      v_9529 <- evaluateAddress v_2891;
      v_9530 <- load v_9529 32;
      setRegister (lhs.of_reg v_2893) (concat (mux (isBitClear v_9525 0) (extract v_9527 0 32) (extract v_9530 0 32)) (concat (mux (isBitClear v_9525 1) (extract v_9527 32 64) (extract v_9530 32 64)) (concat (mux (isBitClear v_9525 2) (extract v_9527 64 96) (extract v_9530 64 96)) (concat (mux (isBitClear v_9525 3) (extract v_9527 96 128) (extract v_9530 96 128)) (concat (mux (isBitClear v_9525 4) (extract v_9527 128 160) (extract v_9530 128 160)) (concat (mux (isBitClear v_9525 5) (extract v_9527 160 192) (extract v_9530 160 192)) (concat (mux (isBitClear v_9525 6) (extract v_9527 192 224) (extract v_9530 192 224)) (mux (isBitClear v_9525 7) (extract v_9527 224 256) (extract v_9530 224 256)))))))));
      pure ()
    pat_end
