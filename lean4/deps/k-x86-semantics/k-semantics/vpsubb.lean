def vpsubb1 : instruction :=
  definst "vpsubb" $ do
    pattern fun (v_2477 : reg (bv 128)) (v_2478 : reg (bv 128)) (v_2479 : reg (bv 128)) => do
      v_4006 <- getRegister v_2478;
      v_4008 <- getRegister v_2477;
      setRegister (lhs.of_reg v_2479) (concat (sub (extract v_4006 0 8) (extract v_4008 0 8)) (concat (sub (extract v_4006 8 16) (extract v_4008 8 16)) (concat (sub (extract v_4006 16 24) (extract v_4008 16 24)) (concat (sub (extract v_4006 24 32) (extract v_4008 24 32)) (concat (sub (extract v_4006 32 40) (extract v_4008 32 40)) (concat (sub (extract v_4006 40 48) (extract v_4008 40 48)) (concat (sub (extract v_4006 48 56) (extract v_4008 48 56)) (concat (sub (extract v_4006 56 64) (extract v_4008 56 64)) (concat (sub (extract v_4006 64 72) (extract v_4008 64 72)) (concat (sub (extract v_4006 72 80) (extract v_4008 72 80)) (concat (sub (extract v_4006 80 88) (extract v_4008 80 88)) (concat (sub (extract v_4006 88 96) (extract v_4008 88 96)) (concat (sub (extract v_4006 96 104) (extract v_4008 96 104)) (concat (sub (extract v_4006 104 112) (extract v_4008 104 112)) (concat (sub (extract v_4006 112 120) (extract v_4008 112 120)) (sub (extract v_4006 120 128) (extract v_4008 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2488 : reg (bv 256)) (v_2489 : reg (bv 256)) (v_2490 : reg (bv 256)) => do
      v_4077 <- getRegister v_2489;
      v_4079 <- getRegister v_2488;
      setRegister (lhs.of_reg v_2490) (concat (sub (extract v_4077 0 8) (extract v_4079 0 8)) (concat (sub (extract v_4077 8 16) (extract v_4079 8 16)) (concat (sub (extract v_4077 16 24) (extract v_4079 16 24)) (concat (sub (extract v_4077 24 32) (extract v_4079 24 32)) (concat (sub (extract v_4077 32 40) (extract v_4079 32 40)) (concat (sub (extract v_4077 40 48) (extract v_4079 40 48)) (concat (sub (extract v_4077 48 56) (extract v_4079 48 56)) (concat (sub (extract v_4077 56 64) (extract v_4079 56 64)) (concat (sub (extract v_4077 64 72) (extract v_4079 64 72)) (concat (sub (extract v_4077 72 80) (extract v_4079 72 80)) (concat (sub (extract v_4077 80 88) (extract v_4079 80 88)) (concat (sub (extract v_4077 88 96) (extract v_4079 88 96)) (concat (sub (extract v_4077 96 104) (extract v_4079 96 104)) (concat (sub (extract v_4077 104 112) (extract v_4079 104 112)) (concat (sub (extract v_4077 112 120) (extract v_4079 112 120)) (concat (sub (extract v_4077 120 128) (extract v_4079 120 128)) (concat (sub (extract v_4077 128 136) (extract v_4079 128 136)) (concat (sub (extract v_4077 136 144) (extract v_4079 136 144)) (concat (sub (extract v_4077 144 152) (extract v_4079 144 152)) (concat (sub (extract v_4077 152 160) (extract v_4079 152 160)) (concat (sub (extract v_4077 160 168) (extract v_4079 160 168)) (concat (sub (extract v_4077 168 176) (extract v_4079 168 176)) (concat (sub (extract v_4077 176 184) (extract v_4079 176 184)) (concat (sub (extract v_4077 184 192) (extract v_4079 184 192)) (concat (sub (extract v_4077 192 200) (extract v_4079 192 200)) (concat (sub (extract v_4077 200 208) (extract v_4079 200 208)) (concat (sub (extract v_4077 208 216) (extract v_4079 208 216)) (concat (sub (extract v_4077 216 224) (extract v_4079 216 224)) (concat (sub (extract v_4077 224 232) (extract v_4079 224 232)) (concat (sub (extract v_4077 232 240) (extract v_4079 232 240)) (concat (sub (extract v_4077 240 248) (extract v_4079 240 248)) (sub (extract v_4077 248 256) (extract v_4079 248 256)))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2471 : Mem) (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) => do
      v_10166 <- getRegister v_2472;
      v_10168 <- evaluateAddress v_2471;
      v_10169 <- load v_10168 16;
      setRegister (lhs.of_reg v_2473) (concat (sub (extract v_10166 0 8) (extract v_10169 0 8)) (concat (sub (extract v_10166 8 16) (extract v_10169 8 16)) (concat (sub (extract v_10166 16 24) (extract v_10169 16 24)) (concat (sub (extract v_10166 24 32) (extract v_10169 24 32)) (concat (sub (extract v_10166 32 40) (extract v_10169 32 40)) (concat (sub (extract v_10166 40 48) (extract v_10169 40 48)) (concat (sub (extract v_10166 48 56) (extract v_10169 48 56)) (concat (sub (extract v_10166 56 64) (extract v_10169 56 64)) (concat (sub (extract v_10166 64 72) (extract v_10169 64 72)) (concat (sub (extract v_10166 72 80) (extract v_10169 72 80)) (concat (sub (extract v_10166 80 88) (extract v_10169 80 88)) (concat (sub (extract v_10166 88 96) (extract v_10169 88 96)) (concat (sub (extract v_10166 96 104) (extract v_10169 96 104)) (concat (sub (extract v_10166 104 112) (extract v_10169 104 112)) (concat (sub (extract v_10166 112 120) (extract v_10169 112 120)) (sub (extract v_10166 120 128) (extract v_10169 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2482 : Mem) (v_2483 : reg (bv 256)) (v_2484 : reg (bv 256)) => do
      v_10233 <- getRegister v_2483;
      v_10235 <- evaluateAddress v_2482;
      v_10236 <- load v_10235 32;
      setRegister (lhs.of_reg v_2484) (concat (sub (extract v_10233 0 8) (extract v_10236 0 8)) (concat (sub (extract v_10233 8 16) (extract v_10236 8 16)) (concat (sub (extract v_10233 16 24) (extract v_10236 16 24)) (concat (sub (extract v_10233 24 32) (extract v_10236 24 32)) (concat (sub (extract v_10233 32 40) (extract v_10236 32 40)) (concat (sub (extract v_10233 40 48) (extract v_10236 40 48)) (concat (sub (extract v_10233 48 56) (extract v_10236 48 56)) (concat (sub (extract v_10233 56 64) (extract v_10236 56 64)) (concat (sub (extract v_10233 64 72) (extract v_10236 64 72)) (concat (sub (extract v_10233 72 80) (extract v_10236 72 80)) (concat (sub (extract v_10233 80 88) (extract v_10236 80 88)) (concat (sub (extract v_10233 88 96) (extract v_10236 88 96)) (concat (sub (extract v_10233 96 104) (extract v_10236 96 104)) (concat (sub (extract v_10233 104 112) (extract v_10236 104 112)) (concat (sub (extract v_10233 112 120) (extract v_10236 112 120)) (concat (sub (extract v_10233 120 128) (extract v_10236 120 128)) (concat (sub (extract v_10233 128 136) (extract v_10236 128 136)) (concat (sub (extract v_10233 136 144) (extract v_10236 136 144)) (concat (sub (extract v_10233 144 152) (extract v_10236 144 152)) (concat (sub (extract v_10233 152 160) (extract v_10236 152 160)) (concat (sub (extract v_10233 160 168) (extract v_10236 160 168)) (concat (sub (extract v_10233 168 176) (extract v_10236 168 176)) (concat (sub (extract v_10233 176 184) (extract v_10236 176 184)) (concat (sub (extract v_10233 184 192) (extract v_10236 184 192)) (concat (sub (extract v_10233 192 200) (extract v_10236 192 200)) (concat (sub (extract v_10233 200 208) (extract v_10236 200 208)) (concat (sub (extract v_10233 208 216) (extract v_10236 208 216)) (concat (sub (extract v_10233 216 224) (extract v_10236 216 224)) (concat (sub (extract v_10233 224 232) (extract v_10236 224 232)) (concat (sub (extract v_10233 232 240) (extract v_10236 232 240)) (concat (sub (extract v_10233 240 248) (extract v_10236 240 248)) (sub (extract v_10233 248 256) (extract v_10236 248 256)))))))))))))))))))))))))))))))));
      pure ()
    pat_end
