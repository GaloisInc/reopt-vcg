def vpunpckhbw : instruction :=
  definst "vpunpckhbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_4 0 8) (extract v_5 0 8)) (concat (concat (extract v_4 8 16) (extract v_5 8 16)) (concat (concat (extract v_4 16 24) (extract v_5 16 24)) (concat (concat (extract v_4 24 32) (extract v_5 24 32)) (concat (concat (extract v_4 32 40) (extract v_5 32 40)) (concat (concat (extract v_4 40 48) (extract v_5 40 48)) (concat (concat (extract v_4 48 56) (extract v_5 48 56)) (concat (extract v_4 56 64) (extract v_5 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (extract v_4 0 8) (extract v_5 0 8)) (concat (concat (extract v_4 8 16) (extract v_5 8 16)) (concat (concat (extract v_4 16 24) (extract v_5 16 24)) (concat (concat (extract v_4 24 32) (extract v_5 24 32)) (concat (concat (extract v_4 32 40) (extract v_5 32 40)) (concat (concat (extract v_4 40 48) (extract v_5 40 48)) (concat (concat (extract v_4 48 56) (extract v_5 48 56)) (concat (concat (extract v_4 56 64) (extract v_5 56 64)) (concat (concat (extract v_4 128 136) (extract v_5 128 136)) (concat (concat (extract v_4 136 144) (extract v_5 136 144)) (concat (concat (extract v_4 144 152) (extract v_5 144 152)) (concat (concat (extract v_4 152 160) (extract v_5 152 160)) (concat (concat (extract v_4 160 168) (extract v_5 160 168)) (concat (concat (extract v_4 168 176) (extract v_5 168 176)) (concat (concat (extract v_4 176 184) (extract v_5 176 184)) (concat (extract v_4 184 192) (extract v_5 184 192)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_3 0 8) (extract v_4 0 8)) (concat (concat (extract v_3 8 16) (extract v_4 8 16)) (concat (concat (extract v_3 16 24) (extract v_4 16 24)) (concat (concat (extract v_3 24 32) (extract v_4 24 32)) (concat (concat (extract v_3 32 40) (extract v_4 32 40)) (concat (concat (extract v_3 40 48) (extract v_4 40 48)) (concat (concat (extract v_3 48 56) (extract v_4 48 56)) (concat (extract v_3 56 64) (extract v_4 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (extract v_3 0 8) (extract v_4 0 8)) (concat (concat (extract v_3 8 16) (extract v_4 8 16)) (concat (concat (extract v_3 16 24) (extract v_4 16 24)) (concat (concat (extract v_3 24 32) (extract v_4 24 32)) (concat (concat (extract v_3 32 40) (extract v_4 32 40)) (concat (concat (extract v_3 40 48) (extract v_4 40 48)) (concat (concat (extract v_3 48 56) (extract v_4 48 56)) (concat (concat (extract v_3 56 64) (extract v_4 56 64)) (concat (concat (extract v_3 128 136) (extract v_4 128 136)) (concat (concat (extract v_3 136 144) (extract v_4 136 144)) (concat (concat (extract v_3 144 152) (extract v_4 144 152)) (concat (concat (extract v_3 152 160) (extract v_4 152 160)) (concat (concat (extract v_3 160 168) (extract v_4 160 168)) (concat (concat (extract v_3 168 176) (extract v_4 168 176)) (concat (concat (extract v_3 176 184) (extract v_4 176 184)) (concat (extract v_3 184 192) (extract v_4 184 192)))))))))))))))));
      pure ()
    pat_end
