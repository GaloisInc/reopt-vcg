def vpackusdw1 : instruction :=
  definst "vpackusdw" $ do
    pattern fun (v_3290 : reg (bv 128)) (v_3291 : reg (bv 128)) (v_3292 : reg (bv 128)) => do
      v_6997 <- getRegister v_3290;
      v_6998 <- eval (extract v_6997 0 32);
      v_7004 <- eval (extract v_6997 32 64);
      v_7010 <- eval (extract v_6997 64 96);
      v_7016 <- eval (extract v_6997 96 128);
      v_7022 <- getRegister v_3291;
      v_7023 <- eval (extract v_7022 0 32);
      v_7029 <- eval (extract v_7022 32 64);
      v_7035 <- eval (extract v_7022 64 96);
      v_7041 <- eval (extract v_7022 96 128);
      setRegister (lhs.of_reg v_3292) (concat (mux (sgt v_6998 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6998 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6997 16 32))) (concat (mux (sgt v_7004 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7004 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6997 48 64))) (concat (mux (sgt v_7010 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7010 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6997 80 96))) (concat (mux (sgt v_7016 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7016 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6997 112 128))) (concat (mux (sgt v_7023 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7023 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7022 16 32))) (concat (mux (sgt v_7029 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7029 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7022 48 64))) (concat (mux (sgt v_7035 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7035 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7022 80 96))) (mux (sgt v_7041 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7041 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7022 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3301 : reg (bv 256)) (v_3302 : reg (bv 256)) (v_3303 : reg (bv 256)) => do
      v_7060 <- getRegister v_3301;
      v_7061 <- eval (extract v_7060 0 32);
      v_7067 <- eval (extract v_7060 32 64);
      v_7073 <- eval (extract v_7060 64 96);
      v_7079 <- eval (extract v_7060 96 128);
      v_7085 <- getRegister v_3302;
      v_7086 <- eval (extract v_7085 0 32);
      v_7092 <- eval (extract v_7085 32 64);
      v_7098 <- eval (extract v_7085 64 96);
      v_7104 <- eval (extract v_7085 96 128);
      v_7110 <- eval (extract v_7060 128 160);
      v_7116 <- eval (extract v_7060 160 192);
      v_7122 <- eval (extract v_7060 192 224);
      v_7128 <- eval (extract v_7060 224 256);
      v_7134 <- eval (extract v_7085 128 160);
      v_7140 <- eval (extract v_7085 160 192);
      v_7146 <- eval (extract v_7085 192 224);
      v_7152 <- eval (extract v_7085 224 256);
      setRegister (lhs.of_reg v_3303) (concat (mux (sgt v_7061 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7061 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 16 32))) (concat (mux (sgt v_7067 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7067 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 48 64))) (concat (mux (sgt v_7073 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7073 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 80 96))) (concat (mux (sgt v_7079 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7079 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 112 128))) (concat (mux (sgt v_7086 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7086 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 16 32))) (concat (mux (sgt v_7092 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7092 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 48 64))) (concat (mux (sgt v_7098 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7098 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 80 96))) (concat (mux (sgt v_7104 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7104 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 112 128))) (concat (mux (sgt v_7110 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7110 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 144 160))) (concat (mux (sgt v_7116 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7116 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 176 192))) (concat (mux (sgt v_7122 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7122 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 208 224))) (concat (mux (sgt v_7128 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7128 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7060 240 256))) (concat (mux (sgt v_7134 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7134 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 144 160))) (concat (mux (sgt v_7140 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7140 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 176 192))) (concat (mux (sgt v_7146 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7146 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 208 224))) (mux (sgt v_7152 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7152 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_7085 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3286 : reg (bv 128)) (v_3287 : reg (bv 128)) => do
      v_12677 <- evaluateAddress v_3285;
      v_12678 <- load v_12677 16;
      v_12679 <- eval (extract v_12678 0 32);
      v_12685 <- eval (extract v_12678 32 64);
      v_12691 <- eval (extract v_12678 64 96);
      v_12697 <- eval (extract v_12678 96 128);
      v_12703 <- getRegister v_3286;
      v_12704 <- eval (extract v_12703 0 32);
      v_12710 <- eval (extract v_12703 32 64);
      v_12716 <- eval (extract v_12703 64 96);
      v_12722 <- eval (extract v_12703 96 128);
      setRegister (lhs.of_reg v_3287) (concat (mux (sgt v_12679 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12679 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12678 16 32))) (concat (mux (sgt v_12685 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12685 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12678 48 64))) (concat (mux (sgt v_12691 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12691 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12678 80 96))) (concat (mux (sgt v_12697 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12697 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12678 112 128))) (concat (mux (sgt v_12704 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12704 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12703 16 32))) (concat (mux (sgt v_12710 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12710 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12703 48 64))) (concat (mux (sgt v_12716 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12716 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12703 80 96))) (mux (sgt v_12722 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12722 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12703 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3296 : Mem) (v_3297 : reg (bv 256)) (v_3298 : reg (bv 256)) => do
      v_12736 <- evaluateAddress v_3296;
      v_12737 <- load v_12736 32;
      v_12738 <- eval (extract v_12737 0 32);
      v_12744 <- eval (extract v_12737 32 64);
      v_12750 <- eval (extract v_12737 64 96);
      v_12756 <- eval (extract v_12737 96 128);
      v_12762 <- getRegister v_3297;
      v_12763 <- eval (extract v_12762 0 32);
      v_12769 <- eval (extract v_12762 32 64);
      v_12775 <- eval (extract v_12762 64 96);
      v_12781 <- eval (extract v_12762 96 128);
      v_12787 <- eval (extract v_12737 128 160);
      v_12793 <- eval (extract v_12737 160 192);
      v_12799 <- eval (extract v_12737 192 224);
      v_12805 <- eval (extract v_12737 224 256);
      v_12811 <- eval (extract v_12762 128 160);
      v_12817 <- eval (extract v_12762 160 192);
      v_12823 <- eval (extract v_12762 192 224);
      v_12829 <- eval (extract v_12762 224 256);
      setRegister (lhs.of_reg v_3298) (concat (mux (sgt v_12738 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12738 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 16 32))) (concat (mux (sgt v_12744 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12744 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 48 64))) (concat (mux (sgt v_12750 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12750 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 80 96))) (concat (mux (sgt v_12756 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12756 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 112 128))) (concat (mux (sgt v_12763 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12763 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 16 32))) (concat (mux (sgt v_12769 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12769 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 48 64))) (concat (mux (sgt v_12775 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12775 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 80 96))) (concat (mux (sgt v_12781 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12781 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 112 128))) (concat (mux (sgt v_12787 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12787 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 144 160))) (concat (mux (sgt v_12793 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12793 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 176 192))) (concat (mux (sgt v_12799 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12799 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 208 224))) (concat (mux (sgt v_12805 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12805 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12737 240 256))) (concat (mux (sgt v_12811 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12811 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 144 160))) (concat (mux (sgt v_12817 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12817 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 176 192))) (concat (mux (sgt v_12823 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12823 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 208 224))) (mux (sgt v_12829 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12829 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_12762 240 256))))))))))))))))));
      pure ()
    pat_end
