def vcmpps1 : instruction :=
  definst "vcmpps" $ do
    pattern fun (v_3022 : imm int) (v_3026 : reg (bv 128)) (v_3027 : reg (bv 128)) (v_3028 : reg (bv 128)) => do
      v_5577 <- getRegister v_3027;
      v_5579 <- getRegister v_3026;
      v_5581 <- eval (handleImmediateWithSignExtend v_3022 8 8);
      setRegister (lhs.of_reg v_3028) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5577 0 32) (extract v_5579 0 32) v_5581) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5577 32 64) (extract v_5579 32 64) v_5581) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5577 64 96) (extract v_5579 64 96) v_5581) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5577 96 128) (extract v_5579 96 128) v_5581) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3035 : imm int) (v_3036 : reg (bv 256)) (v_3037 : reg (bv 256)) (v_3038 : reg (bv 256)) => do
      v_5610 <- getRegister v_3037;
      v_5612 <- getRegister v_3036;
      v_5614 <- eval (handleImmediateWithSignExtend v_3035 8 8);
      setRegister (lhs.of_reg v_3038) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 0 32) (extract v_5612 0 32) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 32 64) (extract v_5612 32 64) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 64 96) (extract v_5612 64 96) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 96 128) (extract v_5612 96 128) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 128 160) (extract v_5612 128 160) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 160 192) (extract v_5612 160 192) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 192 224) (extract v_5612 192 224) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_5610 224 256) (extract v_5612 224 256) v_5614) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_3016 : imm int) (v_3017 : Mem) (v_3020 : reg (bv 128)) (v_3021 : reg (bv 128)) => do
      v_9749 <- getRegister v_3020;
      v_9751 <- evaluateAddress v_3017;
      v_9752 <- load v_9751 16;
      v_9754 <- eval (handleImmediateWithSignExtend v_3016 8 8);
      setRegister (lhs.of_reg v_3021) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9749 0 32) (extract v_9752 0 32) v_9754) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9749 32 64) (extract v_9752 32 64) v_9754) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9749 64 96) (extract v_9752 64 96) v_9754) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9749 96 128) (extract v_9752 96 128) v_9754) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3029 : imm int) (v_3030 : Mem) (v_3031 : reg (bv 256)) (v_3032 : reg (bv 256)) => do
      v_9777 <- getRegister v_3031;
      v_9779 <- evaluateAddress v_3030;
      v_9780 <- load v_9779 32;
      v_9782 <- eval (handleImmediateWithSignExtend v_3029 8 8);
      setRegister (lhs.of_reg v_3032) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 0 32) (extract v_9780 0 32) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 32 64) (extract v_9780 32 64) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 64 96) (extract v_9780 64 96) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 96 128) (extract v_9780 96 128) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 128 160) (extract v_9780 128 160) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 160 192) (extract v_9780 160 192) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 192 224) (extract v_9780 192 224) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (_(_,_,_)_MINT-WRAPPER-SYNTAX cmp_single_pred (extract v_9777 224 256) (extract v_9780 224 256) v_9782) (expression.bv_nat 1 1)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
